/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Moore.ScalarOuter

@[expose] public section

/-! A determinant bound for the two outer products in the logarithmic Hessian. -/

noncomputable section
namespace KakeyaSharp.Moore
open Matrix KakeyaSharp.QuaternionAlgebra

theorem outer_mul_self {n : ℕ} (g : Fin n → Quaternion ℝ) :
    outer g * outer g = quaternionSize g • outer g := by
  have hs : (∑ i, star (g i) * g i) = (quaternionSize g : Quaternion ℝ) := by
    simp only [Quaternion.star_mul_self, quaternionSize,
      Quaternion.normSq_eq_norm_mul_self, pow_two]
    simpa only [Quaternion.algebraMap_def] using
      (map_sum (algebraMap ℝ (Quaternion ℝ)) (fun i => ‖g i‖ * ‖g i‖) Finset.univ).symm
  apply Matrix.ext
  intro i j
  change (∑ k, (g i * star (g k)) * (g k * star (g j))) =
    quaternionSize g • (g i * star (g j))
  calc
    _ = g i * (∑ k, star (g k) * g k) * star (g j) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      noncomm_ring
    _ = _ := by rw [hs]; simp [Quaternion.mul_coe_eq_smul]

theorem quaternion_re_mul_comm (p q : Quaternion ℝ) : (p * q).re = (q * p).re := by
  simp only [Quaternion.re_mul]
  ring

theorem trace_mul_outer {n : ℕ} (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (w : Fin n → Quaternion ℝ) :
    (∑ i, ((A * outer w) i i).re) = quaternionForm A w := by
  simp only [quaternionForm, Matrix.mul_apply, Matrix.mulVec, dotProduct, outer,
    Finset.mul_sum, quaternion_re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, quaternion_re_mul_comm]

def scalarOuterBase {n : ℕ} (c s : ℝ) (g : Fin n → Quaternion ℝ) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) := c • 1 - s • outer g

def scalarOuterInverse {n : ℕ} (c a s : ℝ) (g : Fin n → Quaternion ℝ) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
  (1 / c) • 1 + (s / (c * a)) • outer g

theorem scalarOuterBase_hermitian {n : ℕ} (c s : ℝ) (g : Fin n → Quaternion ℝ) :
    (scalarOuterBase c s g).IsHermitian := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    ext <;> simp [scalarOuterBase, Matrix.conjTranspose_apply, outer]
  · ext <;> simp [scalarOuterBase, Matrix.conjTranspose_apply, outer,
      hij, Ne.symm hij]

theorem scalarOuterBase_mul_inverse {n : ℕ} (g : Fin n → Quaternion ℝ)
    {c a : ℝ} (hc : c ≠ 0) (ha : a ≠ 0) (s : ℝ)
    (he : a = c - s * quaternionSize g) :
    scalarOuterBase c s g * scalarOuterInverse c a s g = 1 := by
  have h1 : c * (1 / c) = 1 := by field_simp
  have h2 : c * (s / (c * a)) - s * (1 / c) -
      s * (s / (c * a)) * quaternionSize g = 0 := by
    field_simp
    rw [he]
    ring
  simp only [scalarOuterBase, scalarOuterInverse, Matrix.sub_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    outer_mul_self]
  calc
    _ = (c * (1 / c)) • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) +
        (c * (s / (c * a)) - s * (1 / c) -
          s * (s / (c * a)) * quaternionSize g) • outer g := by module
    _ = 1 := by rw [h1, h2]; simp

theorem scalarOuterInverse_mul_base {n : ℕ} (g : Fin n → Quaternion ℝ)
    {c a : ℝ} (hc : c ≠ 0) (ha : a ≠ 0) (s : ℝ)
    (he : a = c - s * quaternionSize g) :
    scalarOuterInverse c a s g * scalarOuterBase c s g = 1 := by
  have hcomm : scalarOuterInverse c a s g * scalarOuterBase c s g =
      scalarOuterBase c s g * scalarOuterInverse c a s g := by
    simp only [scalarOuterBase, scalarOuterInverse, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  rw [hcomm, scalarOuterBase_mul_inverse g hc ha s he]

theorem scalarOuterInverse_form_le {n : ℕ} (g w : Fin n → Quaternion ℝ)
    {c a s : ℝ} (hc : 0 < c) (ha : 0 < a) (hs : 0 ≤ s)
    (he : a = c - s * quaternionSize g) :
    quaternionForm (scalarOuterInverse c a s g) w ≤ (1 / a) * quaternionSize w := by
  rw [scalarOuterInverse, quaternionForm_add, quaternionForm_smul,
    quaternionForm_smul, quaternionForm_one]
  have h := mul_le_mul_of_nonneg_left (quaternionForm_outer_le g w)
    (show 0 ≤ s / (c * a) by positivity)
  have he' : 1 / c + s / (c * a) * quaternionSize g = 1 / a := by
    field_simp
    nlinarith [he]
  calc
    _ ≤ (1 / c) * quaternionSize w +
        (s / (c * a)) * (quaternionSize g * quaternionSize w) := by linarith
    _ = (1 / c + s / (c * a) * quaternionSize g) * quaternionSize w := by ring
    _ = _ := by rw [he']

theorem mooreDet_scalarOuterBase {n : ℕ} (hn : 1 ≤ n)
    (g : Fin n → Quaternion ℝ) {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    mooreDet n (scalarOuterBase c s g) = c ^ (n - 1) * (c - s * quaternionSize g) := by
  rw [scalarOuterBase, sub_eq_add_neg, ← neg_smul, mooreDet_scalar_outer hn g hc]
  ring

/-- The cofactor of `c I - s gg*` is bounded above by `c^(n-1) I`. -/
theorem mooreDet_rankTwo_bound {n : ℕ} (hn : 1 ≤ n)
    (g w : Fin n → Quaternion ℝ) {c a s t : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (he : a = c - s * quaternionSize g) :
    mooreDet n (scalarOuterBase c s g + t • outer w) ≤
      c ^ (n - 1) * (a + t * quaternionSize w) := by
  have hd : mooreDet n (scalarOuterBase c s g) = c ^ (n - 1) * a := by
    rw [mooreDet_scalarOuterBase hn g hc.ne', ← he]
  have hdiff := mooreDifferential_inverse n (scalarOuterBase c s g) (outer w)
    (scalarOuterInverse c a s g) (scalarOuterBase_hermitian c s g)
    (outer_isHermitian w) (scalarOuterBase_mul_inverse g hc.ne' ha.ne' s he)
    (scalarOuterInverse_mul_base g hc.ne' ha.ne' s he)
  rw [trace_mul_outer, hd] at hdiff
  have hi := mul_le_mul_of_nonneg_left (scalarOuterInverse_form_le g w hc ha hs he)
    (show 0 ≤ c ^ (n - 1) * a by positivity)
  have hb : mooreDifferential n (scalarOuterBase c s g) (outer w) ≤
      c ^ (n - 1) * quaternionSize w := by
    rw [hdiff]
    convert hi using 1
    field_simp
  rw [mooreDet_add_outer_differential, hd]
  have h := mul_le_mul_of_nonneg_left hb ht
  nlinarith only [h]

end KakeyaSharp.Moore
