/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.CompactLocalExtension
public import KakeyaSharp.ThinValueSmoothLocal

@[expose] public section

/-! Local equality preserves the admissible solutions, current equations,
and the variational value needed for local smooth extensions. -/
noncomputable section
namespace KakeyaSharp
open Set Filter MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Green
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem thinSlice_eventuallyEq {m : ℕ} {U V : ThinCurrentSpace m → ℝ}
    {p : Space 3} {z : ThinSpace m} (h : U =ᶠ[𝓝 (p,z)] V) :
    thinSlice U p =ᶠ[𝓝 z] thinSlice V p := by
  have hc : Continuous (fun x : ThinSpace m => (p,x)) := by fun_prop
  exact h.comp_tendsto (hc.tendsto z)

theorem ThinAdmissibleAt.congr_nhds {m : ℕ} {R : ℝ} {o : ThinSpace m}
    {f g : ThinSpace m → ℝ} (hf : ThinAdmissibleAt R o f)
    (h : ∀ z ∈ thinClosedBallAt R o, g =ᶠ[𝓝 z] f) : ThinAdmissibleAt R o g := by
  refine ⟨fun z hz => (hf.1 z hz).congr_of_eventuallyEq (h z hz), ?_, ?_⟩
  · intro z hz
    rw [(h z (show z ∈ thinClosedBallAt R o from hz.le)).self_of_nhds]
    exact hf.2.1 z hz
  · intro z hz w
    rw [thinQuaternionHessian_congr_nhds (h z hz)]
    exact hf.2.2 z hz w

theorem thinValueRealAt_congr_source {m : ℕ} (R : ℝ) (o : ThinSpace m)
    {ρ σ : ThinSpace m → ℝ} (h : ∀ z ∈ thinBallAt R o, ρ z = σ z) :
    thinValueRealAt R o ρ = thinValueRealAt R o σ := by
  have he (f : ThinSpace m → ℝ) : thinFunctionalAt R o ρ f = thinFunctionalAt R o σ f := by
    unfold thinFunctionalAt
    congr 1
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only
    rw [h z hz]
  unfold thinValueRealAt thinVariationalValueAt
  simp_rw [he]

theorem RealColumnConservationOn.congr_nhds {m : ℕ} {D : Set (ThinCurrentSpace m)}
    {A B : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : RealColumnConservationOn D A) (h : ∀ y ∈ D, B =ᶠ[𝓝 y] A) :
    RealColumnConservationOn D B := by
  intro y hy q
  have he (p : Fin (m+1) × Fin 3) :
      fderiv ℝ (fun x => realCoefficients threeSlots (B x) p q) y =
        fderiv ℝ (fun x => realCoefficients threeSlots (A x) p q) y := by
    apply Filter.EventuallyEq.fderiv_eq
    exact (h y hy).mono (fun x hx => congrArg
      (fun M : Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ) =>
        realCoefficients threeSlots M p q) hx)
  simp_rw [he]
  exact hA y hy q

end KakeyaSharp
