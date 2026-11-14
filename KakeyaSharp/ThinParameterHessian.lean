/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinCurrent
public import KakeyaSharp.Calculus.SliceDerivatives

@[expose] public section

/-! Differentiating a spatial Moore determinant in the three actual parameter
directions. A smooth solution family is an explicit hypothesis; no existence
or parameter regularity theorem for the Dirichlet problem is assumed as an axiom. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Calculus
open scoped ContDiff Matrix.Norms.Elementwise

def thinSlice {m : ℕ} (U : ThinCurrentSpace m → ℝ) (p : Space 3) : ThinSpace m → ℝ :=
  fun z => U (p,z)

def thinParameterDerivative {m : ℕ} (U : ThinCurrentSpace m → ℝ) (a : Fin 3)
    (p : Space 3) (z : ThinSpace m) : ℝ :=
  fderiv ℝ U (p,z) (parameterDirection a)

def thinFamilyHessian {m : ℕ} (U : ThinCurrentSpace m → ℝ)
    (y : ThinCurrentSpace m) : Matrix (Fin m) (Fin m) (Quaternion ℝ) :=
  thinQuaternionHessian (thinSlice U y.1) y.2

theorem thinSlice_contDiff {m : ℕ} {n : ℕ∞ω} {U : ThinCurrentSpace m → ℝ}
    (hU : ContDiff ℝ n U) (p : Space 3) : ContDiff ℝ n (thinSlice U p) :=
  hU.comp (contDiff_const.prodMk contDiff_id)

theorem thinParameterDerivative_contDiff {m : ℕ} {U : ThinCurrentSpace m → ℝ}
    (hU : ContDiff ℝ 3 U) (a : Fin 3) (p : Space 3) :
    ContDiff ℝ 2 (thinParameterDerivative U a p) :=
  (contDiff_directionalDerivative (n := 2) hU (parameterDirection a)).comp
    (contDiff_const.prodMk contDiff_id)

theorem thinFamilyHessian_eq {m : ℕ} {U : ThinCurrentSpace m → ℝ}
    (hU : ContDiff ℝ 2 U) :
    thinFamilyHessian U = directionalHessian threeSlots spatialDirection U := by
  funext y
  unfold thinFamilyHessian thinQuaternionHessian directionalHessian
  congr 1
  apply Matrix.ext
  intro a b
  exact secondDerivative_slice_right hU y.1 y.2 (thinDirection a.1 a.2) (thinDirection b.1 b.2)

theorem fderiv_thinFamilyHessian {m : ℕ} {U : ThinCurrentSpace m → ℝ}
    (hU : ContDiff ℝ 3 U) (p : Space 3) (z : ThinSpace m) (a : Fin 3) :
    fderiv ℝ (thinFamilyHessian U) (p,z) (parameterDirection a) =
      thinQuaternionHessian (thinParameterDerivative U a p) z := by
  rw [thinFamilyHessian_eq (hU.of_le (by norm_num)),
    fderiv_directionalHessian_apply threeSlots spatialDirection hU]
  rw [← thinFamilyHessian_eq (contDiff_directionalDerivative (n := 2) hU (parameterDirection a))]
  rfl

theorem fderiv_mooreDet_apply (m : ℕ)
    (H D : Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    fderiv ℝ (mooreDet m) H D = mooreDifferential m H D := by
  have hl : HasDerivAt (fun t : ℝ => H + t • D) D 0 := by
    simpa only [id_eq, one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add H
  have h₁ := ((contDiff_mooreDet m 1).differentiable (by norm_num) (H + 0 • D)).hasFDerivAt.comp_hasDerivAt 0 hl
  have h₂ := hasDerivAt_mooreDet_path m (fun t : ℝ => H + t • D) D 0
    (fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hl i) j)
  simpa only [zero_smul, add_zero] using! h₁.unique h₂

theorem fderiv_thinFamilyDet {m : ℕ} {U : ThinCurrentSpace m → ℝ}
    (hU : ContDiff ℝ 3 U) (p : Space 3) (z : ThinSpace m) (a : Fin 3) :
    fderiv ℝ (fun y => mooreDet m (thinFamilyHessian U y)) (p,z) (parameterDirection a) =
      mooreDifferential m (thinQuaternionHessian (thinSlice U p) z)
        (thinQuaternionHessian (thinParameterDerivative U a p) z) := by
  have hH : DifferentiableAt ℝ (thinFamilyHessian U) (p,z) := by
    rw [thinFamilyHessian_eq (hU.of_le (by norm_num))]
    exact (hasFDerivAt_directionalHessian threeSlots spatialDirection hU.contDiffAt).differentiableAt
  have hc := fderiv_comp (p,z)
    ((contDiff_mooreDet m 1).differentiable (by norm_num) _) hH
  change fderiv ℝ (mooreDet m ∘ thinFamilyHessian U) (p,z) (parameterDirection a) = _
  rw [hc, ContinuousLinearMap.comp_apply]
  have h := congrArg (fun D => fderiv ℝ (mooreDet m) (thinFamilyHessian U (p,z)) D)
    (fderiv_thinFamilyHessian hU p z a)
  exact h.trans (fderiv_mooreDet_apply m _ _)

theorem thinSolution_linearized {m : ℕ} {R : ℝ} (o : ThinSpace m)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U) (hρ : ContDiff ℝ 1 ρ)
    (hEq : ∀ p z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z))
    (p : Space 3) (z : ThinSpace m) (hz : z ∈ thinBallAt R o) (a : Fin 3) :
    mooreDifferential m (thinQuaternionHessian (thinSlice U p) z)
      (thinQuaternionHessian (thinParameterDerivative U a p) z) =
        fderiv ℝ ρ (p,z) (parameterDirection a) := by
  have hH : DifferentiableAt ℝ (thinFamilyHessian U) (p,z) := by
    rw [thinFamilyHessian_eq (hU.of_le (by norm_num))]
    exact (hasFDerivAt_directionalHessian threeSlots spatialDirection hU.contDiffAt).differentiableAt
  have hd := ((contDiff_mooreDet m 1).differentiable (by norm_num) _).comp (p,z) hH
  have he : (fun q => mooreDet m (thinFamilyHessian U (q,z))) = (fun q => ρ (q,z)) :=
    funext (fun q => hEq q z hz)
  have h := congrArg (fun f => fderiv ℝ f p (EuclideanSpace.single a 1)) he
  change fderiv ℝ (fun q => (mooreDet m ∘ thinFamilyHessian U) (q,z)) p
    (EuclideanSpace.single a 1) = _ at h
  rw [fderiv_slice_left hd, fderiv_slice_left (hρ.differentiable (by norm_num) (p,z))] at h
  change fderiv ℝ (fun y => mooreDet m (thinFamilyHessian U y)) (p,z) (parameterDirection a) =
    fderiv ℝ ρ (p,z) (parameterDirection a) at h
  rwa [fderiv_thinFamilyDet hU] at h

theorem thinParameterDerivative_boundary {m : ℕ} {R : ℝ} (o : ThinSpace m)
    {U : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 1 U)
    (hb : ∀ p z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0)
    (p : Space 3) (a : Fin 3) (z : ThinSpace m)
    (hz : ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2) : thinParameterDerivative U a p z = 0 := by
  have he : (fun q => U (q,z)) = (fun _ => (0 : ℝ)) := funext (fun q => hb q z hz)
  have h := congrArg (fun f => fderiv ℝ f p (EuclideanSpace.single a 1)) he
  rw [fderiv_slice_left (hU.differentiable (by norm_num) (p,z)), fderiv_const_apply] at h
  exact h

end KakeyaSharp
