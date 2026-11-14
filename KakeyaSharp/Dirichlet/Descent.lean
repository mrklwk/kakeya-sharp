/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Dirichlet.Existence
public import KakeyaSharp.Dirichlet.Translation
public import OAI.Analysis.PDE.Dirichlet.Rough.RegularityGlobal

@[expose] public section

/-! Descent from the periodic four-coordinate problem to the original
three-coordinate ball, including the equation and positivity on its boundary. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Dirichlet
open Set Matrix Filter
open scoped ContDiff Topology ComplexOrder

theorem reconstruct {m : ℕ} (x : FullSpace m) :
    embed m (project m x) + fourthShift m (split m x).1 = x := by
  apply (split m).injective
  simp [embed, fourthShift, project]

theorem invariant_eq_lift {m : ℕ} {R : ℝ} {ψ : FullSpace m → ℝ}
    (hi : ∀ w x, defining R x ≤ 0 → ψ (x+fourthShift m w) = ψ x) :
    ∀ x, defining R x ≤ 0 → ψ x = ψ (embed m (project m x)) := by
  intro x hx
  have he := hi (split m x).1 (embed m (project m x))
    (by simpa [defining] using hx)
  rwa [reconstruct] at he

theorem invariant_hessian_descends {m : ℕ} {R : ℝ} (hR : 0 < R)
    {ψ : FullSpace m → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hi : ∀ w x, defining R x ≤ 0 → ψ (x+fourthShift m w) = ψ x)
    (x : FullSpace m) (hx : defining R x ≤ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian
      OAI.Analysis.Calculus.Quaternion.fourSlots ψ x =
      thinQuaternionHessian (fun z => ψ (embed m z)) (project m x) := by
  let g : FullSpace m → ℝ := fun y => ψ (embed m (project m y))
  have hg : ContDiff ℝ 2 g := hψ.comp ((embed m).contDiff.comp (project m).contDiff)
  have hΩ : IsOpen {y : FullSpace m | defining R y < 0} :=
    isOpen_lt (defining_smooth R).continuous continuous_const
  have hsubset : {y : FullSpace m | defining R y < 0} ⊆ {y | defining R y ≤ 0} :=
    fun y (hy : defining R y < 0) => hy.le
  have hclosure : {y : FullSpace m | defining R y ≤ 0} ⊆ closure {y | defining R y < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular (defining R)
      ((defining_smooth R).of_le (by norm_num)) (defining_regular hR)]
  have hj := OAI.Analysis.PDE.Dirichlet.first_second_eqOn_of_eqOn_dense_interior
    hΩ hsubset hclosure hψ hg (fun y hy => invariant_eq_lift hi y hy)
  have he : OAI.Analysis.PDE.Dirichlet.quaternionHessian
      OAI.Analysis.Calculus.Quaternion.fourSlots ψ x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian
        OAI.Analysis.Calculus.Quaternion.fourSlots g x := by
    unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian
    congr 1
    unfold OAI.Analysis.PDE.Dirichlet.realHessian
    rw [hj.2 hx]
  exact he.trans (hessian_lift (hψ.comp (embed m).contDiff) x)

theorem exists_thin_ball_C4 (m : ℕ) {R : ℝ} (hR : 0 < R)
    {ρ : ThinSpace (m+1) → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ z ∈ thinClosedBallAt R 0, 0 < ρ z) :
    ∃ u : ThinSpace (m+1) → ℝ, ContDiff ℝ 4 u ∧
      (∀ z, ‖z.1‖^2 + ‖z.2‖^2 = R^2 → u z = 0) ∧
      (∀ z ∈ thinClosedBallAt R 0,
        (KakeyaSharp.Moore.complexify (thinQuaternionHessian u z)).PosDef) ∧
      (∀ z ∈ thinClosedBallAt R 0,
        KakeyaSharp.Moore.mooreDet (m+1) (thinQuaternionHessian u z) = ρ z) := by
  obtain ⟨ψ,hψ,hp,hb,hpos,hdet⟩ := exists_periodic_ball_C4 m hR hρ hρpos
  let u : ThinSpace (m+1) → ℝ := fun z => ψ (embed (m+1) z)
  have hu : ContDiff ℝ 4 u := hψ.comp (embed (m+1)).contDiff
  have hi := solution_fourth_invariant (by omega : 1 ≤ m+1) hR
    (hψ.of_le (by norm_num)) hp hb hpos hdet
  have hclosed (z : ThinSpace (m+1)) (hz : z ∈ thinClosedBallAt R 0) :
      defining R (embed (m+1) z) ≤ 0 :=
    (defining_nonpos_iff R _).mpr (by simpa using hz)
  have he (z : ThinSpace (m+1)) (hz : z ∈ thinClosedBallAt R 0) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian
        OAI.Analysis.Calculus.Quaternion.fourSlots ψ (embed (m+1) z) =
        thinQuaternionHessian u z := by
    simpa [u] using invariant_hessian_descends hR (hψ.of_le (by norm_num)) hi
      (embed (m+1) z) (hclosed z hz)
  refine ⟨u,hu,?_,?_,?_⟩
  · intro z hz
    exact hb _ (by simp [defining, hz])
  · intro z hz
    rw [complexify_eq_upstream, ← he z hz]
    exact hpos _ (hclosed z hz)
  · intro z hz
    rw [mooreDet_eq_upstream, ← he z hz]
    simpa using hdet _ (hclosed z hz)

end KakeyaSharp.Dirichlet
