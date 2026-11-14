/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Dirichlet.Solution
public import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Local

@[expose] public section

/-! Gluing the joint boundary representatives on a compact parameter
neighborhood. Values and actual spatial Hessians agree on the closed ball. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp.Dirichlet
open Set Metric Filter
open scoped ContDiff Topology

theorem thinBallAt_zero_closure {m : ℕ} {R : ℝ} (hR : 0 < R) :
    closure (thinBallAt R (0 : ThinSpace m)) = thinClosedBallAt R 0 := by
  let d : ThinSpace m → ℝ := fun z => ‖z.1‖^2+‖z.2‖^2-R^2
  have hd : ContDiff ℝ 1 d := by
    exact ((contDiff_fst.norm_sq (𝕜 := ℝ)).add
      (contDiff_snd.norm_sq (𝕜 := ℝ))).sub contDiff_const
  have hreg : ∀ z, d z = 0 → fderiv ℝ d z ≠ 0 := by
    intro z hz he
    have h := (((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).norm_sq).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).norm_sq)).sub_const (R^2)
    have hh := congrArg (fun L => L z) h.fderiv
    change fderiv ℝ d z z = _ at hh
    rw [he] at hh
    simp at hh
    dsimp [d] at hz
    nlinarith [sq_pos_of_pos hR]
  simpa only [d, thinBallAt, thinClosedBallAt, Prod.fst_zero, Prod.snd_zero,
    sub_zero, sub_lt_zero, sub_nonpos] using
    OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular d hd hreg

theorem thinHessian_eqOn_closed_of_eqOn {m : ℕ} {R : ℝ} (hR : 0 < R)
    {u v : ThinSpace m → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (he : EqOn u v (thinClosedBallAt R 0)) :
    EqOn (thinQuaternionHessian u) (thinQuaternionHessian v) (thinClosedBallAt R 0) := by
  have hsub : thinBallAt R (0 : ThinSpace m) ⊆ thinClosedBallAt R 0 := by
    intro z hz
    exact (show ‖z.1-0‖^2+‖z.2-0‖^2 < R^2 from hz).le
  have hj := OAI.Analysis.PDE.Dirichlet.first_second_eqOn_of_eqOn_dense_interior
    (thinBallAt_isOpen R (0 : ThinSpace m)) hsub
    (by rw [thinBallAt_zero_closure hR]) hu hv he
  intro z hz
  unfold thinQuaternionHessian thinRealHessian
  rw [hj.2 hz]

theorem exists_local_joint_representative {m : ℕ} {R : ℝ} (hR : 0 < R)
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω) {U : ThinCurrentSpace m → ℝ}
    (hs : ∀ p ∈ Ω, ContDiff ℝ 2 (thinSlice U p))
    (hl : ∀ p ∈ Ω, ∀ z ∈ thinClosedBallAt R 0,
      ∃ O : Set (ThinCurrentSpace m), IsOpen O ∧ (p,z) ∈ O ∧
        ∃ g : ThinCurrentSpace m → ℝ, ContDiffOn ℝ 3 g O ∧
          ∀ q ∈ O, q.1 ∈ Ω → q.2 ∈ thinClosedBallAt R 0 → g q = U q)
    {p : Space 3} (hp : p ∈ Ω) :
    ∃ W : Set (Space 3), IsOpen W ∧ p ∈ W ∧ W ⊆ Ω ∧
      ∃ V : ThinCurrentSpace m → ℝ, ContDiff ℝ 3 V ∧
        (∀ q ∈ W, ∀ z ∈ thinClosedBallAt R 0, V (q,z) = U (q,z)) ∧
        (∀ q ∈ W, ∀ z ∈ thinClosedBallAt R 0,
          thinQuaternionHessian (thinSlice V q) z =
            thinQuaternionHessian (thinSlice U q) z) := by
  obtain ⟨r,hr,hrΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hp)
  have hcΩ : closedBall p (r/2) ⊆ Ω := by
    intro q hq
    apply hrΩ
    exact lt_of_le_of_lt (show dist q p ≤ r/2 from hq) (by linarith)
  let K := closedBall p (r/2) ×ˢ thinClosedBallAt R (0 : ThinSpace m)
  have hK : IsClosed K := isClosed_closedBall.prod
    (thinClosedBallAt_compact hR.le (0 : ThinSpace m)).isClosed
  obtain ⟨V,hV,he⟩ :=
    OAI.Analysis.Calculus.SmoothExtension.exists_contDiff_extension_of_local_on hK 3 U (by
      rintro ⟨q,z⟩ ⟨hq,hz⟩
      obtain ⟨O,hO,hqz,g,hg,hge⟩ := hl q (hcΩ hq) z hz
      exact ⟨O,hO,hqz,g,hg,fun y hy => hge y hy.2 (hcΩ hy.1.1) hy.1.2⟩)
  refine ⟨ball p (r/2),isOpen_ball,mem_ball_self (by linarith),
    fun q hq => hcΩ (ball_subset_closedBall hq),V,hV,?_,?_⟩
  · intro q hq z hz
    exact he (q,z) ⟨ball_subset_closedBall hq,hz⟩
  · intro q hq
    exact thinHessian_eqOn_closed_of_eqOn hR
      (thinSlice_contDiff (hV.of_le (by norm_num)) q)
      (hs q (hcΩ (ball_subset_closedBall hq)))
      (fun z hz => he (q,z) ⟨ball_subset_closedBall hq,hz⟩)

end KakeyaSharp.Dirichlet
