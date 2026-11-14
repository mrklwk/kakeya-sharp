/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinValueDerivative

@[expose] public section

/-! Actual second coordinate derivatives of the variational supremum and
their cofactor energy identity. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
namespace KakeyaSharp
open Set MeasureTheory KakeyaSharp.Moore KakeyaSharp.Calculus KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

theorem hasDerivAt_thinValueRealAt_parameter_deriv {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U) (hρ : ContDiff ℝ 2 ρ)
    (hadm : ∀ p, ThinAdmissibleAt R o (thinSlice U p))
    (hEq : ∀ p z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z))
    (p : Space 3) (a : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => deriv (fun r => thinValueRealAt R o (thinSlice ρ (parameterLine p a r))) s)
      (-(∫ z in thinBallAt R o,
        thinParameterDerivative U a (parameterLine p a t) z *
          fderiv ℝ ρ (parameterLine p a t,z) (parameterDirection a) +
        U (parameterLine p a t,z) * fderiv ℝ (fderiv ℝ ρ) (parameterLine p a t,z)
          (parameterDirection a) (parameterDirection a))) t := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hDρ : ContDiff ℝ 1 (fun y => fderiv ℝ ρ y (parameterDirection a)) :=
    contDiff_directionalDerivative (n := 1) hρ (parameterDirection a)
  have he : (fun s => deriv (fun r => thinValueRealAt R o (thinSlice ρ (parameterLine p a r))) s) =
      (fun s => -(∫ z in thinBallAt R o,
        U (parameterLine p a s,z) * fderiv ℝ ρ (parameterLine p a s,z) (parameterDirection a))) := by
    funext s
    exact (hasDerivAt_thinValueRealAt_parameter hR o hU hρ1 hadm hEq p a s).deriv
  rw [he]
  have hd := (hasDerivAt_thinParameterIntegral hR o (hU1.mul hDρ) p a t).neg
  convert hd using 1
  congr 1
  apply setIntegral_congr_fun (thinBallAt_measurable R o)
  intro z _
  have hh := ((hU1.differentiable (by norm_num) (parameterLine p a t,z)).hasFDerivAt.mul
    (hDρ.differentiable (by norm_num) (parameterLine p a t,z)).hasFDerivAt).fderiv
  have h := congrArg (fun L => L (parameterDirection a)) hh
  change fderiv ℝ (fun y => U y * fderiv ℝ ρ y (parameterDirection a))
      (parameterLine p a t,z) (parameterDirection a) =
    U (parameterLine p a t,z) * fderiv ℝ (fun y => fderiv ℝ ρ y (parameterDirection a))
      (parameterLine p a t,z) (parameterDirection a) +
    fderiv ℝ ρ (parameterLine p a t,z) (parameterDirection a) *
      fderiv ℝ U (parameterLine p a t,z) (parameterDirection a) at h
  dsimp only
  rw [h, directional_twice hρ]
  dsimp only [thinParameterDerivative]
  ring

theorem thinValueRealAt_parameter_curvature {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U) (hρ : ContDiff ℝ 2 ρ)
    (hadm : ∀ p, ThinAdmissibleAt R o (thinSlice U p))
    (hEq : ∀ p z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z))
    (p : Space 3) (a : Fin 3) :
    deriv (deriv (fun t => thinValueRealAt R o (thinSlice ρ (parameterLine p a t)))) 0 =
      (∫ z in thinBallAt R o, quaternionForm (thinCofactor (thinSlice U p) z)
        (thinQuaternionGradient (thinParameterDerivative U a p) z)) -
      ∫ z in thinBallAt R o, U (p,z) *
        fderiv ℝ (fderiv ℝ ρ) (p,z) (parameterDirection a) (parameterDirection a) := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hDρ : ContDiff ℝ 1 (fun y => fderiv ℝ ρ y (parameterDirection a)) :=
    contDiff_directionalDerivative (n := 1) hρ (parameterDirection a)
  have hDDρ : Continuous (fun y => fderiv ℝ (fderiv ℝ ρ) y (parameterDirection a)
      (parameterDirection a)) := by
    exact ((hρ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const |>.clm_apply continuous_const
  have hb : ∀ p z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0 :=
    fun p => (hadm p).2.1
  have hG := thinCofactor_energy_identity hR o (thinSlice_contDiff hU p)
    (thinParameterDerivative_contDiff hU a p)
    (fun z hz => thinParameterDerivative_boundary o (hU.of_le (by norm_num)) hb p a z hz)
  have hG' : -(∫ z in thinBallAt R o, thinParameterDerivative U a p z *
      fderiv ℝ ρ (p,z) (parameterDirection a)) =
      ∫ z in thinBallAt R o, quaternionForm (thinCofactor (thinSlice U p) z)
        (thinQuaternionGradient (thinParameterDerivative U a p) z) := by
    rw [← hG, ← integral_neg]
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only
    rw [thinSolution_linearized o hU hρ1 hEq p z hz a, neg_mul]
  have hi₁ : IntegrableOn (fun z => thinParameterDerivative U a p z *
      fderiv ℝ ρ (p,z) (parameterDirection a)) (thinBallAt R o) :=
    continuous_integrableOn_thinBallAt hR o ((thinParameterDerivative_contDiff hU a p).continuous.mul
      (hDρ.continuous.comp (continuous_const.prodMk continuous_id)))
  have hi₂ : IntegrableOn (fun z => U (p,z) *
      fderiv ℝ (fderiv ℝ ρ) (p,z) (parameterDirection a) (parameterDirection a)) (thinBallAt R o) :=
    continuous_integrableOn_thinBallAt hR o ((thinSlice_contDiff hU p).continuous.mul
      (hDDρ.comp (continuous_const.prodMk continuous_id)))
  have h := (hasDerivAt_thinValueRealAt_parameter_deriv hR o hU hρ hadm hEq p a 0).deriv
  rw [show parameterLine p a 0 = p by simp [parameterLine]] at h
  change deriv (deriv (fun t => thinValueRealAt R o (thinSlice ρ (parameterLine p a t)))) 0 = _ at h
  rw [h, integral_add hi₁ hi₂, neg_add, hG', sub_eq_add_neg]

end KakeyaSharp
