/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinHessian
public import KakeyaSharp.QuaternionPositive

@[expose] public section

/-! Strict quaternionic positivity of the logarithmic test. -/

noncomputable section
namespace KakeyaSharp
open KakeyaSharp.QuaternionAlgebra Matrix

theorem thinProfile_quaternionHessian_hermitian {m : ℕ} {η : ℝ} (hη : 0 < η)
    {z : ThinSpace m} (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) :
    (thinQuaternionHessian (thinProfile η) z).IsHermitian := by
  rw [thinProfile_quaternionHessian hη hz]
  have hs (A : Matrix (Fin m) (Fin m) (Quaternion ℝ))
      (hA : A.IsHermitian) (c : ℝ) : (c • A).IsHermitian := by
    apply Matrix.ext
    intro i j
    change star (c • A j i) = c • A i j
    rw [Quaternion.star_smul]
    exact congrArg (fun q => c • q) (congrFun (congrFun hA i) j)
  exact (((hs 1 isHermitian_one _).sub
    (hs _ (outer_isHermitian _) _)).add
    (hs 1 isHermitian_one _)).add
    (hs _ (outer_isHermitian _) _)

/-- An explicit positive lower bound for the quadratic form of the Hessian. -/
theorem thinProfile_quaternionHessian_lower {m : ℕ} {η : ℝ} (hη : 0 < η)
    {z : ThinSpace m} (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1)
    (w : Fin m → Quaternion ℝ) :
    (4 * η ^ 2 / thinNumerator η z ^ 2 + 2 / thinDenominator η z) *
        quaternionSize w ≤ quaternionForm (thinQuaternionHessian (thinProfile η) z) w := by
  have hb := thinNumerator_pos hη z
  have hcs := quaternionForm_outer_le (thinPGradient z) w
  have hgn : quaternionSize (thinPGradient z) = 4 * ‖z.2‖ ^ 2 :=
    thinPGradient_norm_sq z
  rw [hgn] at hcs
  have hx : 0 ≤ quaternionForm (outer (thinXVector z)) w := by
    rw [quaternionForm_outer]
    positivity
  have hc : 4 / thinNumerator η z - 4 * ‖z.2‖ ^ 2 / thinNumerator η z ^ 2 =
      4 * η ^ 2 / thinNumerator η z ^ 2 := by
    field_simp
    unfold thinNumerator
    ring
  rw [thinProfile_quaternionHessian hη hz, quaternionForm_add, quaternionForm_add,
    quaternionForm_sub, quaternionForm_smul, quaternionForm_smul,
    quaternionForm_smul, quaternionForm_smul, quaternionForm_one]
  have hp := mul_le_mul_of_nonneg_left hcs
    (show 0 ≤ 1 / thinNumerator η z ^ 2 by positivity)
  have hx' := mul_nonneg (show 0 ≤ 4 / thinDenominator η z ^ 2 by positivity) hx
  have hc' := congrArg (fun c => c * quaternionSize w) hc
  simp only [div_eq_mul_inv, one_mul] at hp hx' hc' ⊢
  nlinarith only [hc', hp, hx']

/-- Strict positivity on every nonzero quaternionic vector, in arbitrary dimension. -/
theorem thinProfile_quaternionHessian_positive {m : ℕ} {η : ℝ} (hη : 0 < η)
    {z : ThinSpace m} (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1)
    {w : Fin m → Quaternion ℝ} (hw : w ≠ 0) :
    0 < quaternionForm (thinQuaternionHessian (thinProfile η) z) w := by
  have hb := thinNumerator_pos hη z
  have hd := thinDenominator_pos hη hz
  have hc : 0 < 4 * η ^ 2 / thinNumerator η z ^ 2 + 2 / thinDenominator η z := by
    positivity
  exact (mul_pos hc (quaternionSize_pos hw)).trans_le
    (thinProfile_quaternionHessian_lower hη hz w)

end KakeyaSharp
