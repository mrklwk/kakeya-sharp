/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinConcavity

@[expose] public section

/-! Extension of the actual local smoothness hypotheses to global C³ functions.
The extension agrees on a neighborhood of every point of the closed ball,
so all derivatives and the variational functional on the ball are preserved. -/
noncomputable section
namespace KakeyaSharp
open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem exists_global_contDiff_extension (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} (hK : IsCompact K) {f : E → F}
    (hf : ∀ x ∈ K, ContDiffAt ℝ n f x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  let U : Set E := {x | ContDiffAt ℝ n f x}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    change ContDiffAt ℝ n f x at hx
    exact hx.eventually (by simp)
  have hKU : K ⊆ U := hf
  obtain ⟨V,hVo,hKV,hVU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨W,hWo,hKW,hWV⟩ := hK.exists_isOpen_closure_subset (hVo.mem_nhdsSet.mpr hKV)
  obtain ⟨b,hb,-,hsb,hb1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (n : ℕ∞)) hVo isClosed_closure hWV
  let g : E → F := fun x => b x • f x
  have hgb : ContDiff ℝ n g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hb.contDiffAt.smul hx
    · have hn : x ∉ tsupport b := by
        intro hh
        exact hx (hVU (by simpa only [tsupport, hsb] using hh))
      have he : g =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
        change b y • f y = 0
        simp only [hy, Pi.zero_apply, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨g,hgb,?_⟩
  intro x hx
  filter_upwards [hWo.mem_nhds (hKW hx)] with y hy
  change b y • f y = f y
  rw [(hb1 y).mp (subset_closure hy), one_smul]

/-- The C³ specialization used by the variational calculus. -/
theorem exists_global_C3_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) {f : E → ℝ}
    (hf : ∀ x ∈ K, ContDiffAt ℝ 3 f x) :
    ∃ g : E → ℝ, ContDiff ℝ 3 g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f :=
  exists_global_contDiff_extension 3 hK hf

theorem thinQuaternionHessian_congr_nhds {m : ℕ}
    {f g : ThinSpace m → ℝ} {z : ThinSpace m} (h : f =ᶠ[𝓝 z] g) :
    thinQuaternionHessian f z = thinQuaternionHessian g z :=
  Green.directionalHessian_congr_nhds QuaternionAlgebra.threeSlots
    (fun p => thinDirection p.1 p.2) h

theorem thinFunctionalAt_congr_nhds {m : ℕ} (R : ℝ) (o : ThinSpace m)
    (ρ : ThinSpace m → ℝ) {f g : ThinSpace m → ℝ}
    (h : ∀ z ∈ thinClosedBallAt R o, f =ᶠ[𝓝 z] g) :
    thinFunctionalAt R o ρ f = thinFunctionalAt R o ρ g := by
  have he (z : ThinSpace m) (hz : z ∈ thinBallAt R o) : f =ᶠ[𝓝 z] g :=
    h z (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)
  have hsource : (∫ z in thinBallAt R o, (-f z)*ρ z) =
      ∫ z in thinBallAt R o, (-g z)*ρ z := by
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only
    rw [(he z hz).self_of_nhds]
  have henergy : determinantEnergyAt R o f = determinantEnergyAt R o g := by
    unfold determinantEnergyAt
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only
    rw [(he z hz).self_of_nhds, thinQuaternionHessian_congr_nhds (he z hz)]
  unfold thinFunctionalAt
  rw [hsource, henergy]

end KakeyaSharp

