/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.CurrentIntegrals

@[expose] public section

/-! Two integrations by parts for a matrix of scalar coefficients. -/
noncomputable section
namespace KakeyaSharp.Green
open Set MeasureTheory
open scoped ContDiff

theorem continuous_second_directional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (a b : E) :
    Continuous (fun x => fderiv ℝ (fderiv ℝ f) x a b) :=
  (((hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
    continuous_const).clm_apply continuous_const

theorem integral_double_divergence_transfer
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype I]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {B : Set E} (hB : IsOpen B) (hb : Bornology.IsBounded B) (hnull : μ (frontier B) = 0)
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (hzu : ∀ x ∈ frontier B, u x = 0)
    (d : I → E) (K : I → I → E → ℝ) (hK : ∀ i j, ContDiff ℝ 2 (K i j))
    (hzK : ∀ i j x, x ∈ frontier B → K i j x = 0) :
    (∫ x in B, u x * (∑ i, ∑ j, fderiv ℝ (fderiv ℝ (K i j)) x (d i) (d j)) ∂μ) =
      ∫ x in B, (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ u) x (d j) (d i)) ∂μ := by
  have hl (i j : I) : IntegrableOn
      (fun x => u x * fderiv ℝ (fderiv ℝ (K i j)) x (d i) (d j)) B μ :=
    ((hu.continuous.mul (continuous_second_directional (hK i j) _ _)).continuousOn.integrableOn_compact
      hb.isCompact_closure).mono_set subset_closure
  have hr (i j : I) : IntegrableOn
      (fun x => K i j x * fderiv ℝ (fderiv ℝ u) x (d j) (d i)) B μ :=
    (((hK i j).continuous.mul (continuous_second_directional hu _ _)).continuousOn.integrableOn_compact
      hb.isCompact_closure).mono_set subset_closure
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hl i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hr i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hl i j), integral_finsetSum _ (fun j _ => hr i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_second_derivative_transfer hB hb hnull hu (hK i j) hzu (hzK i j) (d i) (d j)

end KakeyaSharp.Green
