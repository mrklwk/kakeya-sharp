/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinParameterLocal
public import KakeyaSharp.ThinValueCurvature

@[expose] public section

/-! The first and second variation identities need Dirichlet solutions only
on an open parameter domain. The represented value may be arbitrary outside it. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
namespace KakeyaSharp
open Set Filter MeasureTheory KakeyaSharp.Moore KakeyaSharp.Calculus KakeyaSharp.Green
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem parameterLine_mem_eventually {Ω : Set (Space 3)} (hΩ : IsOpen Ω)
    {p : Space 3} {a : Fin 3} {t : ℝ} (ht : parameterLine p a t ∈ Ω) :
    ∀ᶠ s in 𝓝 t, parameterLine p a s ∈ Ω := by
  have hc : Continuous (parameterLine p a) := by unfold parameterLine; fun_prop
  exact hc.continuousAt.eventually (hΩ.mem_nhds ht)

theorem thinSolution_source_linearization_on {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U) (hρ : ContDiff ℝ 1 ρ)
    (hb : ∀ p ∈ Ω, ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0)
    (hEq : ∀ p ∈ Ω, ∀ z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z))
    (p : Space 3) (hp : p ∈ Ω) (a : Fin 3) :
    (∫ z in thinBallAt R o, U (p,z) * fderiv ℝ ρ (p,z) (parameterDirection a)) =
      (m : ℝ) * ∫ z in thinBallAt R o, thinParameterDerivative U a p z * ρ (p,z) := by
  have h := thinEnergy_linearization hR o (thinSlice_contDiff hU p)
    (thinParameterDerivative_contDiff hU a p) (hb p hp)
    (fun z hz => thinParameterDerivative_boundary_on o hΩ (hU.of_le (by norm_num)) hb p hp a z hz)
  convert h using 1
  · apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only [thinSlice]
    rw [thinSolution_linearized_on o hΩ hU hρ hEq p hp z hz a]
  · congr 1
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only
    rw [hEq p hp z hz]

theorem hasDerivAt_thinValueRealAt_parameter_on {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U) (hρ : ContDiff ℝ 1 ρ)
    (hadm : ∀ p ∈ Ω, ThinAdmissibleAt R o (thinSlice U p))
    (hEq : ∀ p ∈ Ω, ∀ z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z))
    (p : Space 3) (a : Fin 3) (t : ℝ) (ht : parameterLine p a t ∈ Ω) :
    HasDerivAt (fun s => thinValueRealAt R o (thinSlice ρ (parameterLine p a s)))
      (-(∫ z in thinBallAt R o,
        U (parameterLine p a t,z) * fderiv ℝ ρ (parameterLine p a t,z) (parameterDirection a))) t := by
  let q := parameterLine p a t
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hb : ∀ p ∈ Ω, ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0 :=
    fun p hp => (hadm p hp).2.1
  have hlin := thinSolution_source_linearization_on hR o hΩ hU hρ hb hEq q ht a
  have hfun : (fun s => thinValueRealAt R o (thinSlice ρ (parameterLine p a s))) =ᶠ[𝓝 t]
      (fun s => (m : ℝ)/((m : ℝ)+1) *
        ∫ z in thinBallAt R o, (-U (parameterLine p a s,z))*ρ (parameterLine p a s,z)) := by
    filter_upwards [parameterLine_mem_eventually hΩ ht] with s hs
    exact thinValueRealAt_PDE_representation hR
      (thinSlice_contDiff hρ _).continuous.continuousOn (hadm _ hs) (hEq _ hs)
  refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
  have hd := (hasDerivAt_thinParameterIntegral hR o (hU1.neg.mul hρ) p a t).const_mul
    ((m : ℝ)/((m : ℝ)+1))
  convert hd using 1
  have hp (z : ThinSpace m) :
      fderiv ℝ (fun y => (-U y)*ρ y) (q,z) (parameterDirection a) =
        -(thinParameterDerivative U a q z * ρ (q,z)) -
          U (q,z) * fderiv ℝ ρ (q,z) (parameterDirection a) := by
    have h := ((hU1.differentiable (by norm_num) (q,z)).hasFDerivAt.neg.mul
      (hρ.differentiable (by norm_num) (q,z)).hasFDerivAt).fderiv
    have he := congrArg (fun L => L (parameterDirection a)) h
    change fderiv ℝ (fun y => (-U y)*ρ y) (q,z) (parameterDirection a) =
      (-U (q,z)) * fderiv ℝ ρ (q,z) (parameterDirection a) +
        ρ (q,z) * (-fderiv ℝ U (q,z) (parameterDirection a)) at he
    rw [he]
    dsimp only [thinParameterDerivative]
    ring
  have hi₁ : IntegrableOn (fun z => thinParameterDerivative U a q z * ρ (q,z)) (thinBallAt R o) :=
    continuous_integrableOn_thinBallAt hR o
      ((thinParameterDerivative_contDiff hU a q).continuous.mul (thinSlice_contDiff hρ q).continuous)
  have hi₂ : IntegrableOn (fun z => U (q,z) * fderiv ℝ ρ (q,z) (parameterDirection a))
      (thinBallAt R o) := continuous_integrableOn_thinBallAt hR o
        ((thinSlice_contDiff hU q).continuous.mul
          ((contDiff_directionalDerivative (n := 0) hρ (parameterDirection a)).continuous.comp
            (continuous_const.prodMk continuous_id)))
  change -(∫ z in thinBallAt R o, U (q,z)*fderiv ℝ ρ (q,z) (parameterDirection a)) = _
  change _ = (m : ℝ)/((m : ℝ)+1) *
    ∫ z in thinBallAt R o, fderiv ℝ (fun y => (-U y)*ρ y) (q,z) (parameterDirection a)
  simp_rw [hp]
  have hiN : IntegrableOn (fun z => -(thinParameterDerivative U a q z * ρ (q,z)))
      (thinBallAt R o) := hi₁.neg
  rw [integral_sub hiN hi₂, integral_neg]
  have hm : (m : ℝ)+1 ≠ 0 := by positivity
  field_simp
  nlinarith [hlin]
theorem hasDerivAt_thinValueRealAt_parameter_deriv_on {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U) (hρ : ContDiff ℝ 2 ρ)
    (hadm : ∀ p ∈ Ω, ThinAdmissibleAt R o (thinSlice U p))
    (hEq : ∀ p ∈ Ω, ∀ z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z))
    (p : Space 3) (a : Fin 3) (t : ℝ) (ht : parameterLine p a t ∈ Ω) :
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
  have he : (fun s => deriv (fun r => thinValueRealAt R o (thinSlice ρ (parameterLine p a r))) s) =ᶠ[𝓝 t]
      (fun s => -(∫ z in thinBallAt R o,
        U (parameterLine p a s,z) * fderiv ℝ ρ (parameterLine p a s,z) (parameterDirection a))) := by
    filter_upwards [parameterLine_mem_eventually hΩ ht] with s hs
    exact (hasDerivAt_thinValueRealAt_parameter_on hR o hΩ hU hρ1 hadm hEq p a s hs).deriv
  refine HasDerivAt.congr_of_eventuallyEq ?_ he
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

theorem thinValueRealAt_parameter_curvature_on {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U) (hρ : ContDiff ℝ 2 ρ)
    (hadm : ∀ p ∈ Ω, ThinAdmissibleAt R o (thinSlice U p))
    (hEq : ∀ p ∈ Ω, ∀ z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z))
    (p : Space 3) (hp : p ∈ Ω) (a : Fin 3) :
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
  have hb : ∀ p ∈ Ω, ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0 :=
    fun p hp => (hadm p hp).2.1
  have hG := thinCofactor_energy_identity hR o (thinSlice_contDiff hU p)
    (thinParameterDerivative_contDiff hU a p)
    (fun z hz => thinParameterDerivative_boundary_on o hΩ (hU.of_le (by norm_num)) hb p hp a z hz)
  have hG' : -(∫ z in thinBallAt R o, thinParameterDerivative U a p z *
      fderiv ℝ ρ (p,z) (parameterDirection a)) =
      ∫ z in thinBallAt R o, quaternionForm (thinCofactor (thinSlice U p) z)
        (thinQuaternionGradient (thinParameterDerivative U a p) z) := by
    rw [← hG, ← integral_neg]
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only
    rw [thinSolution_linearized_on o hΩ hU hρ1 hEq p hp z hz a, neg_mul]
  have hi₁ : IntegrableOn (fun z => thinParameterDerivative U a p z *
      fderiv ℝ ρ (p,z) (parameterDirection a)) (thinBallAt R o) :=
    continuous_integrableOn_thinBallAt hR o ((thinParameterDerivative_contDiff hU a p).continuous.mul
      (hDρ.continuous.comp (continuous_const.prodMk continuous_id)))
  have hi₂ : IntegrableOn (fun z => U (p,z) *
      fderiv ℝ (fderiv ℝ ρ) (p,z) (parameterDirection a) (parameterDirection a)) (thinBallAt R o) :=
    continuous_integrableOn_thinBallAt hR o ((thinSlice_contDiff hU p).continuous.mul
      (hDDρ.comp (continuous_const.prodMk continuous_id)))
  have h := (hasDerivAt_thinValueRealAt_parameter_deriv_on hR o hΩ hU hρ hadm hEq p a 0
    (by simpa only [parameterLine, zero_smul, add_zero] using hp)).deriv
  rw [show parameterLine p a 0 = p by simp [parameterLine]] at h
  change deriv (deriv (fun t => thinValueRealAt R o (thinSlice ρ (parameterLine p a t)))) 0 = _ at h
  rw [h, integral_add hi₁ hi₂, neg_add, hG', sub_eq_add_neg]


end KakeyaSharp
