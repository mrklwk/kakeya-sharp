/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.QuaternionGreen

@[expose] public section

/-! Boundary integration for the first and second conservation equations. -/
noncomputable section
namespace KakeyaSharp.Green
open Set Filter MeasureTheory
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem integral_directional_by_parts_bounded {S : Set E} (hS : IsOpen S)
    (hb : Bornology.IsBounded S) (hnull : μ (frontier S) = 0) {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hz : ∀ x ∈ frontier S, u x = 0) (d : E) :
    (∫ x in S, u x * fderiv ℝ v x d ∂μ) =
      -(∫ x in S, fderiv ℝ u x d * v x ∂μ) := by
  obtain ⟨u',hu',hsu,heu⟩ := exists_compact_extension_on_bounded hb hu
  obtain ⟨v',hv',hsv,hev⟩ := exists_compact_extension_on_bounded hb hv
  have hzu : ∀ x ∈ frontier S, u' x = 0 := by
    intro x hx
    rw [(heu x hx.1).self_of_nhds, hz x hx]
  have h := integral_directional_by_parts_zero_boundary hS hnull hu' hv' hsu hsv hzu d
  have hl : (∫ x in S, u' x * fderiv ℝ v' x d ∂μ) =
      ∫ x in S, u x * fderiv ℝ v x d ∂μ := by
    apply setIntegral_congr_fun hS.measurableSet
    intro x hx
    dsimp only
    rw [(heu x (subset_closure hx)).self_of_nhds, (hev x (subset_closure hx)).fderiv_eq (𝕜 := ℝ)]
  have hr : (∫ x in S, fderiv ℝ u' x d * v' x ∂μ) =
      ∫ x in S, fderiv ℝ u x d * v x ∂μ := by
    apply setIntegral_congr_fun hS.measurableSet
    intro x hx
    dsimp only
    rw [(heu x (subset_closure hx)).fderiv_eq (𝕜 := ℝ), (hev x (subset_closure hx)).self_of_nhds]
  rwa [hl, hr] at h

theorem integral_divergence_by_parts_bounded {I : Type*} [Fintype I]
    {S : Set E} (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : μ (frontier S) = 0)
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hz : ∀ x ∈ frontier S, u x = 0)
    (d : I → E) (F : I → E → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i)) :
    (∫ x in S, u x * (∑ i, fderiv ℝ (F i) x (d i)) ∂μ) =
      -(∫ x in S, ∑ i, fderiv ℝ u x (d i) * F i x ∂μ) := by
  have hl (i : I) : IntegrableOn (fun x => u x * fderiv ℝ (F i) x (d i)) S μ :=
    ((hu.continuous.mul (continuous_directional (hF i) (d i))).continuousOn.integrableOn_compact
      hb.isCompact_closure).mono_set subset_closure
  have hr (i : I) : IntegrableOn (fun x => fderiv ℝ u x (d i) * F i x) S μ :=
    (((continuous_directional hu (d i)).mul (hF i).continuous).continuousOn.integrableOn_compact
      hb.isCompact_closure).mono_set subset_closure
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hl i)]
  simp_rw [integral_directional_by_parts_bounded hS hb hnull hu (hF _) hz]
  rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun i _ => hr i)]

theorem integral_second_derivative_transfer {S : Set E} (hS : IsOpen S)
    (hb : Bornology.IsBounded S) (hnull : μ (frontier S) = 0) {u v : E → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hzu : ∀ x ∈ frontier S, u x = 0) (hzv : ∀ x ∈ frontier S, v x = 0)
    (a b : E) :
    (∫ x in S, u x * fderiv ℝ (fderiv ℝ v) x a b ∂μ) =
      ∫ x in S, v x * fderiv ℝ (fderiv ℝ u) x b a ∂μ := by
  have hDv : ContDiff ℝ 1 (fun x => fderiv ℝ v x b) :=
    (hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDu : ContDiff ℝ 1 (fun x => fderiv ℝ u x a) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h1 := integral_directional_by_parts_bounded hS hb hnull
    (hu.of_le (by norm_num)) hDv hzu a
  have h2 := integral_directional_by_parts_bounded hS hb hnull
    (hv.of_le (by norm_num)) hDu hzv b
  simp only [directional_twice hv] at h1
  simp only [directional_twice hu] at h2
  rw [h1, h2]
  congr 1
  apply setIntegral_congr_fun hS.measurableSet
  intro x _
  exact mul_comm _ _

end KakeyaSharp.Green
