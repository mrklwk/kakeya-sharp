/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.DirectionalCofactor

@[expose] public section

/-! Self-adjointness and the integrated linearization of determinant energy. -/
noncomputable section
namespace KakeyaSharp.Green
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Matrix.Norms.Elementwise

theorem realCoefficients_bilinear_symm {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : A.IsHermitian)
    (ξ ζ : Fin n × Fin s → ℝ) :
    (∑ p, ∑ q, realCoefficients e A p q * ξ p * ζ q) =
      ∑ p, ∑ q, realCoefficients e A p q * ζ p * ξ q := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [(realCoefficients_isSymm e A hA).apply q p]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {n s : ℕ}

theorem moore_cofactor_selfAdjoint_bounded
    (e : Fin s → Quaternion ℝ) (d : Fin n × Fin s → E) {S : Set E}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : μ (frontier S) = 0)
    {ψ u v : E → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hzu : ∀ x ∈ frontier S, u x = 0) (hzv : ∀ x ∈ frontier S, v x = 0) :
    (∫ x in S, u x * mooreDifferential n (directionalHessian e d ψ x)
        (directionalHessian e d v x) ∂μ) =
    ∫ x in S, v x * mooreDifferential n (directionalHessian e d ψ x)
        (directionalHessian e d u x) ∂μ := by
  rw [moore_cofactor_green_bounded e d hS hb hnull hψ
      (hu.of_le (by norm_num)) hv hzu,
    moore_cofactor_green_bounded e d hS hb hnull hψ
      (hv.of_le (by norm_num)) hu hzv]
  congr 1
  apply setIntegral_congr_fun hS.measurableSet
  intro x _
  exact realCoefficients_bilinear_symm e _ (mooreCofactor_isHermitian n _) _ _

theorem moore_energy_linearization_bounded
    (e : Fin s → Quaternion ℝ) (d : Fin n × Fin s → E) {S : Set E}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : μ (frontier S) = 0)
    {u v : E → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 2 v)
    (hzu : ∀ x ∈ frontier S, u x = 0) (hzv : ∀ x ∈ frontier S, v x = 0) :
    (∫ x in S, u x * mooreDifferential n (directionalHessian e d u x)
        (directionalHessian e d v x) ∂μ) =
      (n : ℝ) * ∫ x in S, v x * mooreDet n (directionalHessian e d u x) ∂μ := by
  rw [moore_cofactor_selfAdjoint_bounded e d hS hb hnull hu
    (hu.of_le (by norm_num)) hv hzu hzv]
  simp_rw [mooreDifferential_self]
  calc
    _ = ∫ x in S, (n : ℝ) * (v x * mooreDet n (directionalHessian e d u x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x using by ring
    _ = _ := integral_const_mul _ _

end KakeyaSharp.Green

