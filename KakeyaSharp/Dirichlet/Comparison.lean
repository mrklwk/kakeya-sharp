/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Dirichlet.Solution

@[expose] public section

/-! Comparison on the actual three-coordinate balls, obtained by lifting
to the checked periodic comparison theorem. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Dirichlet
open Set Matrix KakeyaSharp.Moore
open scoped ContDiff ComplexOrder

theorem thin_dirichlet_comparison_zero {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    {f g : ThinSpace m → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfpos : ∀ z ∈ thinBallAt R 0, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian f z) w)
    (hdet : ∀ z ∈ thinBallAt R 0,
      mooreDet m (thinQuaternionHessian g z) ≤ mooreDet m (thinQuaternionHessian f z))
    (hbd : ∀ z : ThinSpace m, ‖z.1‖^2+‖z.2‖^2=R^2 → f z ≤ g z) :
    ∀ z ∈ thinClosedBallAt R 0, f z ≤ g z := by
  have hfl : ContDiff ℝ 2 (fun y => f (project m y)) := hf.comp (project m).contDiff
  have hgl : ContDiff ℝ 2 (fun y => g (project m y)) := hg.comp (project m).contDiff
  have h := OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_comparison_continuous_lattice hm
    (split m) (lattice m) (thinClosedBallAt_compact hR.le (0 : ThinSpace m))
    hfl.contDiffOn hgl.contDiffOn ((defining_smooth R).of_le (by norm_num))
    hfl.continuous.continuousOn hgl.continuous.continuousOn
    (defining_bounded R) (defining_periodic R) (lift_periodic f) (lift_periodic g)
    (fun y _ => defining_hessian_pos R y) ?_ ?_ ?_
  · intro z hz
    simpa only [project_embed] using h (embed m z) ((defining_nonpos_iff R _).mpr (by simpa using hz))
  · intro y hy
    rw [hessian_lift hf,← complexify_eq_upstream]
    exact (complexify_posDef_iff (thinQuaternionHessian_isHermitian hf.contDiffAt)).mpr
      (hfpos _ ((defining_neg_iff R y).mp hy))
  · intro y hy
    rw [hessian_lift hf,hessian_lift hg,← mooreDet_eq_upstream,← mooreDet_eq_upstream]
    exact hdet _ ((defining_neg_iff R y).mp hy)
  · intro y hy
    exact hbd _ (sub_eq_zero.mp hy)

theorem thinQuaternionHessian_comp_add {m : ℕ} (o : ThinSpace m) (f : ThinSpace m → ℝ)
    (z : ThinSpace m) :
    thinQuaternionHessian (fun y => f (y+o)) z = thinQuaternionHessian f (z+o) := by
  simpa only [sub_neg_eq_add] using thinQuaternionHessian_comp_sub (-o) f z

theorem thin_dirichlet_comparison {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {f g : ThinSpace m → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfpos : ∀ z ∈ thinBallAt R o, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian f z) w)
    (hdet : ∀ z ∈ thinBallAt R o,
      mooreDet m (thinQuaternionHessian g z) ≤ mooreDet m (thinQuaternionHessian f z))
    (hbd : ∀ z : ThinSpace m, ‖z.1-o.1‖^2+‖z.2-o.2‖^2=R^2 → f z ≤ g z) :
    ∀ z ∈ thinClosedBallAt R o, f z ≤ g z := by
  have h := thin_dirichlet_comparison_zero hm hR
    (hf.comp (contDiff_id.add contDiff_const)) (hg.comp (contDiff_id.add contDiff_const))
    (f := fun z => f (z+o)) (g := fun z => g (z+o)) ?_ ?_ ?_
  · intro z hz
    simpa only [sub_add_cancel] using h (z-o) (by simpa [thinClosedBallAt] using hz)
  · intro z hz
    rw [thinQuaternionHessian_comp_add]
    exact hfpos _ (by simpa [thinBallAt] using hz)
  · intro z hz
    rw [thinQuaternionHessian_comp_add,thinQuaternionHessian_comp_add]
    exact hdet _ (by simpa [thinBallAt] using hz)
  · intro z hz
    exact hbd _ (by simpa using hz)

/-- Restricting a source to a smaller ball raises its zero-boundary solution. -/
theorem ThinDirichletSolution.le_on_subball {m : ℕ} (hm : 1 ≤ m) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) {o c : ThinSpace m} {ρ : ThinSpace m → ℝ}
    (S : ThinDirichletSolution R o ρ) (T : ThinDirichletSolution r c ρ)
    (hsub : thinClosedBallAt r c ⊆ thinClosedBallAt R o) :
    ∀ z ∈ thinClosedBallAt r c, S.u z ≤ T.u z := by
  apply thin_dirichlet_comparison hm hr c
    (S.regularity.of_le (by norm_num)) (T.regularity.of_le (by norm_num))
  · intro z hz
    exact S.positive z (hsub (show z ∈ thinClosedBallAt r c from
      (show ‖z.1-c.1‖^2+‖z.2-c.2‖^2 < r^2 from hz).le))
  · intro z hz
    have hz' : z ∈ thinClosedBallAt r c :=
      (show ‖z.1-c.1‖^2+‖z.2-c.2‖^2 < r^2 from hz).le
    rw [T.equation z hz',S.equation z (hsub hz')]
  · intro z hz
    rw [T.admissible.2.1 z hz]
    exact S.admissible.nonpos hm hR z (hsub hz.le)

end KakeyaSharp.Dirichlet
