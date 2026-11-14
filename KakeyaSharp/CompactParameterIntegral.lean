/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.CompactVariation

@[expose] public section

/-! Joint parameter regularity for integration over a fixed relatively compact
set. Uniform bounds are proved on compact products, not assumed. -/
noncomputable section
namespace KakeyaSharp
open Set Filter MeasureTheory
open scoped Topology ContDiff

variable {P E V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {S K : Set E}

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem continuous_setIntegral_compact (hS : MeasurableSet S)
    (hK : IsCompact K) (hSK : S ⊆ K) {F : P × E → V} (hF : Continuous F) :
    Continuous (fun p => ∫ z in S, F (p,z) ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod hK).exists_bound_of_continuousOn hF.continuousOn
  have hi : IntegrableOn (fun _ : E => C) S μ :=
    (integrableOn_const (μ := μ) (C := C) (s := K) hK.measure_lt_top.ne).mono_set hSK
  apply continuousAt_of_dominated (F := fun q z => F (q,z))
    (Eventually.of_forall (fun q => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    ?_ hi (Eventually.of_forall (fun z => (hF.comp (continuous_id.prodMk continuous_const)).continuousAt))
  filter_upwards [Metric.ball_mem_nhds p (by norm_num : (0 : ℝ)<1)] with q hq
  filter_upwards [ae_restrict_mem hS] with z hz
  exact hC (q,z) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hq).le,hSK hz⟩

def partialParameterDerivative (F : P × E → V) (y : P × E) : P →L[ℝ] V :=
  (fderiv ℝ F y).comp (ContinuousLinearMap.inl ℝ P E)

omit [ProperSpace P] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem partialParameterDerivative_contDiff {n : ℕ∞ω} {F : P × E → V}
    (hF : ContDiff ℝ (n+1) F) : ContDiff ℝ n (partialParameterDerivative F) :=
  (hF.fderiv_right (m := n) le_rfl).clm_comp contDiff_const

theorem hasFDerivAt_setIntegral_compact (hS : MeasurableSet S)
    (hK : IsCompact K) (hSK : S ⊆ K) {F : P × E → V} (hF : ContDiff ℝ 1 F) (p : P) :
    HasFDerivAt (fun q => ∫ z in S, F (q,z) ∂μ)
      (∫ z in S, partialParameterDerivative F (p,z) ∂μ) p := by
  have hD : Continuous (partialParameterDerivative F) :=
    (partialParameterDerivative_contDiff (n := 0) hF).continuous
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod hK).exists_bound_of_continuousOn hD.continuousOn
  have hi : IntegrableOn (fun _ : E => C) S μ :=
    (integrableOn_const (μ := μ) (C := C) (s := K) hK.measure_lt_top.ne).mono_set hSK
  have hFi : IntegrableOn (fun z => F (p,z)) S μ :=
    ((hF.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK).mono_set hSK
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q z => F (q,z)) (F' := fun q z => partialParameterDerivative F (q,z))
    (Metric.ball_mem_nhds p (by norm_num : (0 : ℝ)<1))
    (Eventually.of_forall (fun q => (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    hFi (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable ?_ hi ?_
  · filter_upwards [ae_restrict_mem hS] with z hz
    intro q hq
    exact hC (q,z) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hq).le,hSK hz⟩
  · apply Eventually.of_forall
    intro z q _
    have h := (hF.differentiable (by norm_num) (q,z)).hasFDerivAt.comp q
      ((hasFDerivAt_id (𝕜 := ℝ) q).prodMk (hasFDerivAt_const z q))
    simpa only [Function.comp_def, id_eq, partialParameterDerivative] using! h

theorem contDiff_one_setIntegral_compact (hS : MeasurableSet S)
    (hK : IsCompact K) (hSK : S ⊆ K) {F : P × E → V} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (fun p => ∫ z in S, F (p,z) ∂μ) := by
  rw [contDiff_one_iff_fderiv]
  constructor
  · exact fun p => (hasFDerivAt_setIntegral_compact hS hK hSK hF p).differentiableAt
  · have he : fderiv ℝ (fun p => ∫ z in S, F (p,z) ∂μ) =
        (fun p => ∫ z in S, partialParameterDerivative F (p,z) ∂μ) :=
      funext (fun p => (hasFDerivAt_setIntegral_compact hS hK hSK hF p).fderiv)
    rw [he]
    exact continuous_setIntegral_compact hS hK hSK
      (partialParameterDerivative_contDiff (n := 0) hF).continuous

theorem contDiff_two_setIntegral_compact (hS : MeasurableSet S)
    (hK : IsCompact K) (hSK : S ⊆ K) {F : P × E → V} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (fun p => ∫ z in S, F (p,z) ∂μ) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  change ContDiff ℝ (1+1) _
  rw [contDiff_succ_iff_fderiv]
  refine ⟨fun p => (hasFDerivAt_setIntegral_compact hS hK hSK hF1 p).differentiableAt, ?_, ?_⟩
  · norm_num
  · have he : fderiv ℝ (fun p => ∫ z in S, F (p,z) ∂μ) =
        (fun p => ∫ z in S, partialParameterDerivative F (p,z) ∂μ) :=
      funext (fun p => (hasFDerivAt_setIntegral_compact hS hK hSK hF1 p).fderiv)
    rw [he]
    exact contDiff_one_setIntegral_compact hS hK hSK (partialParameterDerivative_contDiff (n := 1) hF)

end KakeyaSharp
