/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Dirichlet.Coordinates
public import OAI.Analysis.PDE.Dirichlet.Periodic.Representatives

@[expose] public section

/-! The actual ball-times-torus domain satisfies the geometric hypotheses
of periodic quaternionic Dirichlet solvability. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp.Dirichlet
open Set Matrix Module
open scoped ContDiff ComplexOrder

def lattice (m : ℕ) : Basis (Fin m) ℝ (Space m) := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis

def defining {m : ℕ} (R : ℝ) (x : FullSpace m) : ℝ :=
  ‖(project m x).1‖^2 + ‖(project m x).2‖^2 - R^2

theorem defining_smooth {m : ℕ} (R : ℝ) : ContDiff ℝ ∞ (defining (m := m) R) := by
  exact (((contDiff_fst.comp (project m).contDiff).norm_sq (𝕜 := ℝ)).add
    ((contDiff_snd.comp (project m).contDiff).norm_sq (𝕜 := ℝ))).sub contDiff_const

theorem lift_periodic {m : ℕ} (f : ThinSpace m → ℝ) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (split m) (lattice m)
      (fun x => f (project m x)) := by
  intro x l
  dsimp only
  rw [project_split_symm]
  rfl

theorem defining_periodic {m : ℕ} (R : ℝ) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (split m) (lattice m)
      (defining (m := m) R) :=
  lift_periodic (fun z : ThinSpace m => ‖z.1‖^2 + ‖z.2‖^2 - R^2)

theorem defining_nonpos_iff {m : ℕ} (R : ℝ) (x : FullSpace m) :
    defining R x ≤ 0 ↔ project m x ∈ thinClosedBallAt R 0 := by
  simp [defining, thinClosedBallAt]

theorem defining_neg_iff {m : ℕ} (R : ℝ) (x : FullSpace m) :
    defining R x < 0 ↔ project m x ∈ thinBallAt R 0 := by
  simp [defining, thinBallAt]

theorem defining_bounded {m : ℕ} (R : ℝ) :
    ∀ x : FullSpace m, defining R x ≤ 0 → (split m x).2 ∈ thinClosedBallAt R 0 :=
  fun x hx => (defining_nonpos_iff R x).mp hx

theorem defining_nonempty {m : ℕ} (R : ℝ) :
    {x : FullSpace m | defining R x ≤ 0}.Nonempty := by
  refine ⟨0, ?_⟩
  simp [defining, sq_nonneg]

theorem defining_eq_quadratic {m : ℕ} (R : ℝ) :
    defining (m := m) R = fun x => ((6 : ℝ) • thinQuadraticAt R 0) (project m x) := by
  funext x
  simp [defining, thinQuadraticAt_apply]
  ring

theorem defining_hessian {m : ℕ} (R : ℝ) (x : FullSpace m) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian
      OAI.Analysis.Calculus.Quaternion.fourSlots (defining R) x =
        (6 : ℝ) • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) := by
  rw [defining_eq_quadratic]
  have hs : ContDiff ℝ 2 ((6 : ℝ) • thinQuadraticAt R (0 : ThinSpace m)) :=
    ((thinQuadraticAt_smooth R 0).const_smul (6 : ℝ)).of_le (by norm_num)
  rw [hessian_lift hs, thinQuaternionHessian_smul, thinQuadraticAt_hessian]

theorem defining_hessian_pos {m : ℕ} (R : ℝ) (x : FullSpace m) :
    (OAI.LinearAlgebra.Moore.complexify
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian
        OAI.Analysis.Calculus.Quaternion.fourSlots (defining R) x)).PosDef := by
  rw [defining_hessian, ← complexify_eq_upstream]
  have hH : ((6 : ℝ) • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ))).IsHermitian := by
    apply Matrix.ext
    intro i j
    change star ((6 : ℝ) • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) j i) =
      (6 : ℝ) • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) i j
    rw [Quaternion.star_smul]
    exact congrArg (fun q : Quaternion ℝ => (6 : ℝ) • q)
      ((show (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)).IsHermitian from
        Matrix.isHermitian_one).apply i j)
  apply (KakeyaSharp.Moore.complexify_posDef_iff hH).mpr
  intro w hw
  rw [quaternionForm_smul, quaternionForm_one]
  exact mul_pos (by norm_num) (quaternionSize_pos hw)

theorem defining_derivative_radial {m : ℕ} (R : ℝ) (x : FullSpace m) :
    fderiv ℝ (defining R) x (embed m (project m x)) =
      2 * (‖(project m x).1‖^2 + ‖(project m x).2‖^2) := by
  let L := (ContinuousLinearMap.fst ℝ (Space m) (ThinTransverseSpace m)).comp (project m)
  let M := (ContinuousLinearMap.snd ℝ (Space m) (ThinTransverseSpace m)).comp (project m)
  have h := (((L.hasFDerivAt (x := x)).norm_sq).add
    ((M.hasFDerivAt (x := x)).norm_sq)).sub_const (R^2)
  have he := congrArg (fun A => A (embed m (project m x))) h.fderiv
  change fderiv ℝ (defining R) x (embed m (project m x)) = _ at he
  simpa [L, M, real_inner_self_eq_norm_sq, mul_add] using he

theorem defining_regular {m : ℕ} {R : ℝ} (hR : 0 < R) :
    ∀ x : FullSpace m, defining R x = 0 → fderiv ℝ (defining R) x ≠ 0 := by
  intro x hx hz
  have hd := defining_derivative_radial R x
  rw [hz] at hd
  change 0 = _ at hd
  dsimp [defining] at hx
  nlinarith [sq_pos_of_pos hR]

end KakeyaSharp.Dirichlet
