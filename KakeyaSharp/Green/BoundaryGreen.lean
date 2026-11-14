/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.BoundaryExtension
public import KakeyaSharp.Green.GreenOperator
public import KakeyaSharp.Green.GreenAlgebra

@[expose] public section

/-! Cofactor Green and energy identities with genuine zero boundary values. -/

noncomputable section
namespace KakeyaSharp.Green

open Matrix _root_.MeasureTheory Measure KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped Matrix.Norms.Elementwise

theorem hasCompactSupport_realFlux {E I : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype I] (d : I → E) (K : I → I → E → ℝ)
    {v : E → ℝ} (hv : HasCompactSupport v) (i : I) :
    HasCompactSupport (realFlux d K v i) := by
  apply (hv.fderiv ℝ).mono'
  intro x hx
  by_contra hn
  have hz : fderiv ℝ v x = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hx
  simp only [realFlux, hz, _root_.zero_apply, mul_zero, Finset.sum_const_zero]

theorem real_operator_green_zero_boundary {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype I]
    {μ : Measure E} [IsAddHaarMeasure μ] {S : Set E}
    (hS : IsOpen S) (hnull : μ (frontier S) = 0)
    (d : I → E) (K : I → I → E → ℝ) {u v : E → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hsu : HasCompactSupport u) (hsv : HasCompactSupport v)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (d i) = 0) :
    (∫ x in S, u x * (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x (d i) (d j)) ∂μ) =
      -(∫ x in S, ∑ i, ∑ j, K i j x * fderiv ℝ u x (d i) * fderiv ℝ v x (d j) ∂μ) := by
  have h := integral_divergence_by_parts_zero_boundary hS hnull hu hsu hz d
    (realFlux d K v) (contDiff_realFlux d K hK hv) (hasCompactSupport_realFlux d K hsv)
  simp_rw [realFlux_divergence d K hK hv hdiv] at h
  convert h using 3
  simp only [realFlux, Finset.mul_sum]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


end KakeyaSharp.Green

