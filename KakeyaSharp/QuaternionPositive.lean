/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.QuaternionAlgebra

@[expose] public section

/-! Positivity estimates for quaternionic quadratic forms. -/

noncomputable section
namespace KakeyaSharp
open KakeyaSharp.QuaternionAlgebra Matrix

def quaternionSize {m : ℕ} (w : Fin m → Quaternion ℝ) : ℝ :=
  ∑ i, ‖w i‖ ^ 2

def quaternionForm {m : ℕ} (A : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (w : Fin m → Quaternion ℝ) : ℝ :=
  (∑ i, star (w i) * (A *ᵥ w) i).re

theorem quaternionSize_nonneg {m : ℕ} (w : Fin m → Quaternion ℝ) :
    0 ≤ quaternionSize w := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem quaternionSize_pos {m : ℕ} {w : Fin m → Quaternion ℝ} (hw : w ≠ 0) :
    0 < quaternionSize w := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _,
    sq_pos_of_pos (norm_pos_iff.mpr hi)⟩

theorem quaternion_re_sum {ι : Type*} (s : Finset ι) (f : ι → Quaternion ℝ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

theorem quaternionForm_one {m : ℕ} (w : Fin m → Quaternion ℝ) :
    quaternionForm 1 w = quaternionSize w := by
  simp [quaternionForm, quaternionSize, quaternion_re_sum,
    Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, pow_two]

theorem quaternionForm_outer {m : ℕ} (g w : Fin m → Quaternion ℝ) :
    quaternionForm (outer g) w = ‖∑ i, star (g i) * w i‖ ^ 2 := by
  rw [quaternionForm, outer_quadratic, Quaternion.star_mul_self]
  simp [Quaternion.normSq_eq_norm_mul_self, pow_two]

theorem quaternionForm_add {m : ℕ} (A B : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (w : Fin m → Quaternion ℝ) :
    quaternionForm (A + B) w = quaternionForm A w + quaternionForm B w := by
  simp [quaternionForm, Matrix.add_mulVec, mul_add, Finset.sum_add_distrib]

theorem quaternionForm_sub {m : ℕ} (A B : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (w : Fin m → Quaternion ℝ) :
    quaternionForm (A - B) w = quaternionForm A w - quaternionForm B w := by
  simp [quaternionForm, Matrix.sub_mulVec, mul_sub, Finset.sum_sub_distrib]

theorem quaternionForm_smul {m : ℕ} (c : ℝ)
    (A : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (w : Fin m → Quaternion ℝ) :
    quaternionForm (c • A) w = c * quaternionForm A w := by
  simp [quaternionForm, Matrix.smul_mulVec, ← Finset.smul_sum]

/-- Cauchy--Schwarz for a quaternionic row, obtained without commuting its entries. -/
theorem quaternion_cauchy_schwarz {m : ℕ} (g w : Fin m → Quaternion ℝ) :
    ‖∑ i, star (g i) * w i‖ ^ 2 ≤ quaternionSize g * quaternionSize w := by
  have hn : ‖∑ i, star (g i) * w i‖ ≤ ∑ i, ‖g i‖ * ‖w i‖ := by
    simpa only [norm_mul, norm_star] using
      norm_sum_le Finset.univ (fun i => star (g i) * w i)
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr hn |>.trans
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖g i‖) (fun i => ‖w i‖))

theorem quaternionForm_outer_le {m : ℕ} (g w : Fin m → Quaternion ℝ) :
    quaternionForm (outer g) w ≤ quaternionSize g * quaternionSize w := by
  rw [quaternionForm_outer]
  exact quaternion_cauchy_schwarz g w

end KakeyaSharp
