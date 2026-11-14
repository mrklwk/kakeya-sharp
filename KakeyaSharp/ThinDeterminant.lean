/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinPositive
public import KakeyaSharp.Moore.RankTwoBound

@[expose] public section

/-! Determinant estimates for the actual logarithmic test. -/

noncomputable section
namespace KakeyaSharp
open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore

theorem thinXVector_size {m : ℕ} (z : ThinSpace m) :
    quaternionSize (thinXVector z) = ‖z.1‖ ^ 2 := by
  simp [quaternionSize, thinXVector, EuclideanSpace.real_norm_sq_eq]

def thinHessianBase {m : ℕ} (η : ℝ) (z : ThinSpace m) :
    Matrix (Fin m) (Fin m) (Quaternion ℝ) :=
  scalarOuterBase (4 / thinNumerator η z + 2 / thinDenominator η z)
    (1 / thinNumerator η z ^ 2) (thinPGradient z)

theorem thinHessianBase_small_eigenvalue {m : ℕ} {η : ℝ} (hη : 0 < η)
    {z : ThinSpace m} (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) :
    4 * η ^ 2 / thinNumerator η z ^ 2 + 2 / thinDenominator η z =
      (4 / thinNumerator η z + 2 / thinDenominator η z) -
        (1 / thinNumerator η z ^ 2) * quaternionSize (thinPGradient z) := by
  have hb := thinNumerator_pos hη z
  have hd := thinDenominator_pos hη hz
  rw [show quaternionSize (thinPGradient z) = 4 * ‖z.2‖ ^ 2 from thinPGradient_norm_sq z]
  field_simp
  unfold thinNumerator
  ring

/-- The exact signed determinant before the final positive outer product. -/
theorem thinHessianBase_determinant {m : ℕ} (hm : 1 ≤ m) {η : ℝ} (hη : 0 < η)
    {z : ThinSpace m} (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) :
    mooreDet m (thinHessianBase η z) =
      (4 / thinNumerator η z + 2 / thinDenominator η z) ^ (m - 1) *
        (4 * η ^ 2 / thinNumerator η z ^ 2 + 2 / thinDenominator η z) := by
  have hb := thinNumerator_pos hη z
  have hd := thinDenominator_pos hη hz
  have hc : 0 < 4 / thinNumerator η z + 2 / thinDenominator η z := by positivity
  rw [thinHessianBase, mooreDet_scalarOuterBase hm _ hc.ne',
    ← thinHessianBase_small_eigenvalue hη hz]

theorem thinProfile_quaternionHessian_split {m : ℕ} {η : ℝ} (hη : 0 < η)
    {z : ThinSpace m} (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) :
    thinQuaternionHessian (thinProfile η) z =
      thinHessianBase η z + (4 / thinDenominator η z ^ 2) • outer (thinXVector z) := by
  rw [thinProfile_quaternionHessian hη hz]
  unfold thinHessianBase scalarOuterBase
  module

theorem thinProfile_determinant_prebound {m : ℕ} (hm : 1 ≤ m) {η : ℝ} (hη : 0 < η)
    {z : ThinSpace m} (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) :
    mooreDet m (thinQuaternionHessian (thinProfile η) z) ≤
      (4 / thinNumerator η z + 2 / thinDenominator η z) ^ (m - 1) *
        (4 * η ^ 2 / thinNumerator η z ^ 2 + 2 / thinDenominator η z +
          (4 / thinDenominator η z ^ 2) * ‖z.1‖ ^ 2) := by
  have hb := thinNumerator_pos hη z
  have hd := thinDenominator_pos hη hz
  rw [thinProfile_quaternionHessian_split hη hz, thinHessianBase]
  simpa only [thinXVector_size] using mooreDet_rankTwo_bound hm (thinPGradient z)
    (thinXVector z) (by positivity) (by positivity) (by positivity) (by positivity)
    (thinHessianBase_small_eigenvalue hη hz)

/-- The three integrable determinant kernels, with an explicit dimensional constant. -/
theorem thinProfile_determinant_bound {m : ℕ} (hm : 1 ≤ m) {η : ℝ} (hη : 0 < η)
    {z : ThinSpace m} (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) :
    mooreDet m (thinQuaternionHessian (thinProfile η) z) ≤
      (4 * 6 ^ (m - 1)) * (η ^ 2 / thinNumerator η z ^ (m + 1) +
        1 / (thinDenominator η z * thinNumerator η z ^ (m - 1)) +
        ‖z.1‖ ^ 2 / (thinDenominator η z ^ 2 * thinNumerator η z ^ (m - 1))) := by
  have hb := thinNumerator_pos hη z
  have hd := thinDenominator_pos hη hz
  have hbd : thinNumerator η z ≤ thinDenominator η z := by
    dsimp [thinNumerator, thinDenominator]
    linarith
  have hc : 4 / thinNumerator η z + 2 / thinDenominator η z ≤
      6 / thinNumerator η z := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hb hbd
    calc
      _ ≤ 4 / thinNumerator η z + 2 / thinNumerator η z := add_le_add le_rfl h
      _ = _ := by ring
  have hp := pow_le_pow_left₀
    (show 0 ≤ 4 / thinNumerator η z + 2 / thinDenominator η z by positivity) hc (m - 1)
  have he : thinNumerator η z ^ (m + 1) =
      thinNumerator η z ^ (m - 1) * thinNumerator η z ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ _ := thinProfile_determinant_prebound hm hη hz
    _ ≤ (6 / thinNumerator η z) ^ (m - 1) *
        (4 * η ^ 2 / thinNumerator η z ^ 2 + 2 / thinDenominator η z +
          (4 / thinDenominator η z ^ 2) * ‖z.1‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ _ := by
      apply le_of_sub_nonneg
      convert (show 0 ≤ 2 * 6 ^ (m - 1) /
        (thinDenominator η z * thinNumerator η z ^ (m - 1)) by positivity) using 1
      rw [div_pow, he]
      field_simp
      ring

end KakeyaSharp
