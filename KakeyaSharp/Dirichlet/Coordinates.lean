/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinMaximum
public import OAI.Analysis.PDE.Dirichlet.Hessian
public import OAI.LinearAlgebra.Moore.Basic

@[expose] public section

/-! Explicit separation of the fourth quaternionic coordinates from the
three physical coordinates used by the thin-source problem. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp.Dirichlet

open Matrix Set
open scoped ContDiff ComplexOrder

abbrev FullSpace (m : ℕ) := OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

def splitLinearEquiv (m : ℕ) : FullSpace m ≃ₗ[ℝ] Space m × ThinSpace m where
  toFun z := (WithLp.toLp 2 (fun i => z (i,3)),
    (WithLp.toLp 2 (fun i => z (i,0)),
      WithLp.toLp 2 (fun p => z (p.1,p.2.succ.castSucc))))
  invFun z := WithLp.toLp 2 (fun p =>
    ![z.2.1 p.1, z.2.2 (p.1,0), z.2.2 (p.1,1), z.1 p.1] p.2)
  left_inv z := by
    ext p
    rcases p with ⟨i,a⟩
    fin_cases a <;> rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · ext p
        rcases p with ⟨i,a⟩
        fin_cases a <;> rfl
  map_add' z w := by
    rfl
  map_smul' c z := by
    rfl

def split (m : ℕ) : FullSpace m ≃L[ℝ] Space m × ThinSpace m :=
  (splitLinearEquiv m).toContinuousLinearEquiv

def project (m : ℕ) : FullSpace m →L[ℝ] ThinSpace m :=
  (ContinuousLinearMap.snd ℝ (Space m) (ThinSpace m)).comp (split m).toContinuousLinearMap

def embed (m : ℕ) : ThinSpace m →L[ℝ] FullSpace m :=
  (split m).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Space m) (ThinSpace m))

@[simp] theorem project_embed (m : ℕ) (z : ThinSpace m) : project m (embed m z) = z := by
  change ((split m) ((split m).symm (0,z))).2 = z
  simp

@[simp] theorem project_split_symm (m : ℕ) (w : Space m) (z : ThinSpace m) :
    project m ((split m).symm (w,z)) = z := by
  change ((split m) ((split m).symm (w,z))).2 = z
  simp

@[simp] theorem project_coordinate (m : ℕ) (i : Fin m) (a : Fin 3) :
    project m (OAI.Analysis.PDE.Dirichlet.coordinateVector (i,a.castSucc)) =
      thinDirection i a := by
  fin_cases a <;> apply Prod.ext
  all_goals
    first
    | solve | (ext p; simp [project, split, splitLinearEquiv,
        OAI.Analysis.PDE.Dirichlet.coordinateVector, thinDirection])
    | solve | (ext ⟨j,b⟩; fin_cases b <;> simp [project, split, splitLinearEquiv,
        OAI.Analysis.PDE.Dirichlet.coordinateVector, thinDirection])

@[simp] theorem project_fourth_coordinate (m : ℕ) (i : Fin m) :
    project m (OAI.Analysis.PDE.Dirichlet.coordinateVector (i,3)) = 0 := by
  apply Prod.ext
  · ext p
    simp [project, split, splitLinearEquiv, OAI.Analysis.PDE.Dirichlet.coordinateVector]
  · ext ⟨j,b⟩
    fin_cases b <;>
      simp [project, split, splitLinearEquiv, OAI.Analysis.PDE.Dirichlet.coordinateVector]

theorem mooreDet_eq_upstream (m : ℕ) (A : Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    KakeyaSharp.Moore.mooreDet m A = OAI.LinearAlgebra.Moore.mooreDet m A := rfl

theorem complexify_eq_upstream {m : ℕ} (A : Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    KakeyaSharp.Moore.complexify A = OAI.LinearAlgebra.Moore.complexify A := rfl

theorem secondDerivative_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : F → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (L y))) x v w =
      fderiv ℝ (fderiv ℝ f) (L x) (L v) (L w) := by
  have he : fderiv ℝ (fun y => f (L y)) =
      fun y => (fderiv ℝ f (L y)).comp L := by
    funext y
    exact ((hf.differentiable (by norm_num) (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv
  rw [he]
  have h := (((hf.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) (L x)).hasFDerivAt.comp x L.hasFDerivAt).clm_comp
      (hasFDerivAt_const (𝕜 := ℝ) L x)
  have hh := congrArg (fun A => A v w) h.fderiv
  simpa using hh

theorem hessian_lift {m : ℕ} {f : ThinSpace m → ℝ} (hf : ContDiff ℝ 2 f)
    (x : FullSpace m) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian
      OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => f (project m y)) x =
      thinQuaternionHessian f (project m x) := by
  have h0 (i : Fin m) : project m (OAI.Analysis.PDE.Dirichlet.coordinateVector (i,0)) =
      thinDirection i 0 := project_coordinate m i 0
  have h1 (i : Fin m) : project m (OAI.Analysis.PDE.Dirichlet.coordinateVector (i,1)) =
      thinDirection i 1 := project_coordinate m i 1
  have h2 (i : Fin m) : project m (OAI.Analysis.PDE.Dirichlet.coordinateVector (i,2)) =
      thinDirection i 2 := project_coordinate m i 2
  apply Matrix.ext
  intro i j
  simp [OAI.Analysis.PDE.Dirichlet.quaternionHessian,
    OAI.Analysis.Calculus.Quaternion.hessianMap,
    OAI.Analysis.PDE.Dirichlet.realHessian,
    secondDerivative_comp_linear (project m) hf,
    Fin.sum_univ_four, h0, h1, h2, project_fourth_coordinate,
    thinQuaternionHessian, KakeyaSharp.QuaternionAlgebra.hessianMap,
    thinRealHessian, OAI.Analysis.Calculus.Quaternion.fourSlots,
    KakeyaSharp.QuaternionAlgebra.threeSlots, Fin.sum_univ_three]

end KakeyaSharp.Dirichlet
