/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinParameterHessian

@[expose] public section

/-! Differentiation of the Dirichlet equation and boundary condition when
they hold only on an open parameter domain. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set Filter KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Calculus
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem thinSolution_linearized_on {m : ℕ} {R : ℝ} (o : ThinSpace m)
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U) (hρ : ContDiff ℝ 1 ρ)
    (hEq : ∀ p ∈ Ω, ∀ z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z))
    (p : Space 3) (hp : p ∈ Ω) (z : ThinSpace m) (hz : z ∈ thinBallAt R o) (a : Fin 3) :
    mooreDifferential m (thinQuaternionHessian (thinSlice U p) z)
      (thinQuaternionHessian (thinParameterDerivative U a p) z) =
        fderiv ℝ ρ (p,z) (parameterDirection a) := by
  have hH : DifferentiableAt ℝ (thinFamilyHessian U) (p,z) := by
    rw [thinFamilyHessian_eq (hU.of_le (by norm_num))]
    exact (hasFDerivAt_directionalHessian threeSlots spatialDirection hU.contDiffAt).differentiableAt
  have hd := ((contDiff_mooreDet m 1).differentiable (by norm_num) _).comp (p,z) hH
  have he : (fun q => mooreDet m (thinFamilyHessian U (q,z))) =ᶠ[𝓝 p] (fun q => ρ (q,z)) := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact hEq q hq z hz
  have h := congrArg (fun L => L (EuclideanSpace.single a 1)) (he.fderiv_eq (𝕜 := ℝ))
  change fderiv ℝ (fun q => (mooreDet m ∘ thinFamilyHessian U) (q,z)) p
    (EuclideanSpace.single a 1) = _ at h
  rw [fderiv_slice_left hd, fderiv_slice_left (hρ.differentiable (by norm_num) (p,z))] at h
  change fderiv ℝ (fun y => mooreDet m (thinFamilyHessian U y)) (p,z) (parameterDirection a) =
    fderiv ℝ ρ (p,z) (parameterDirection a) at h
  rwa [fderiv_thinFamilyDet hU] at h

theorem thinParameterDerivative_boundary_on {m : ℕ} {R : ℝ} (o : ThinSpace m)
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω)
    {U : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 1 U)
    (hb : ∀ p ∈ Ω, ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0)
    (p : Space 3) (hp : p ∈ Ω) (a : Fin 3) (z : ThinSpace m)
    (hz : ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2) : thinParameterDerivative U a p z = 0 := by
  have he : (fun q => U (q,z)) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact hb q hq z hz
  have h := congrArg (fun L => L (EuclideanSpace.single a 1)) (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_slice_left (hU.differentiable (by norm_num) (p,z)), fderiv_const_apply] at h
  exact h


end KakeyaSharp
