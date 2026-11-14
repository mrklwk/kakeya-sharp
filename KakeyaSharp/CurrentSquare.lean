/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinPairings

@[expose] public section

/-! The exact positive sum of squares at the end of scalar transfer.
The cofactor is the same signed Moore cofactor as in the variation proofs. -/
noncomputable section
namespace KakeyaSharp
open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green

theorem quaternionForm_vector_add {m : ℕ}
    (H : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (hH : H.IsHermitian)
    (u v : Fin m → Quaternion ℝ) :
    quaternionForm H (u+v) = quaternionForm H u + quaternionForm H v +
      2 * (star u ⬝ᵥ H *ᵥ v).re := by
  have hs := hermitian_dotProduct_real_swap H hH u v
  change (star (u+v) ⬝ᵥ H *ᵥ (u+v)).re =
    (star u ⬝ᵥ H *ᵥ u).re + (star v ⬝ᵥ H *ᵥ v).re + 2 * (star u ⬝ᵥ H *ᵥ v).re
  rw [star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
  simp only [Quaternion.re_add]
  linarith

theorem real_dot_swap {m : ℕ} (u v : Fin m → Quaternion ℝ) :
    (star u ⬝ᵥ v).re = (star v ⬝ᵥ u).re := by
  have h := hermitian_dotProduct_real_swap (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    isHermitian_one u v
  simpa only [Matrix.one_mulVec] using h

theorem quaternionForm_inverse_vector {m : ℕ}
    (H V : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (hHV : H*V=1)
    (w : Fin m → Quaternion ℝ) :
    quaternionForm H (V *ᵥ w) = quaternionForm V w := by
  change (star (V *ᵥ w) ⬝ᵥ H *ᵥ (V *ᵥ w)).re = (star w ⬝ᵥ V *ᵥ w).re
  rw [Matrix.mulVec_mulVec, hHV, Matrix.one_mulVec, real_dot_swap]

theorem quaternionForm_cofactor_inverse {m : ℕ}
    (H V : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (hH : H.IsHermitian)
    (hHV : H*V=1) (hVH : V*H=1) (w : Fin m → Quaternion ℝ) :
    quaternionForm (mooreCofactor m H) w = mooreDet m H * quaternionForm V w := by
  rw [← realTrace_mul_outer, mooreCofactor_pairing m H (outer w) (outer_isHermitian w)]
  rw [mooreDifferential_inverse m H (outer w) V hH (outer_isHermitian w) hHV hVH]
  have he : (∑ i, ((V * outer w) i i).re) = realTrace (V * outer w) := by
    simp only [realTrace, Matrix.trace, Matrix.diag, quaternion_re_sum]
  rw [he, realTrace_mul_outer]

theorem current_square_term {m : ℕ}
    (H V : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (hH : H.IsHermitian)
    (hHV : H*V=1) (b w : Fin m → Quaternion ℝ) :
    quaternionForm H (b+V*ᵥw) = quaternionForm H b + quaternionForm V w +
      2 * (star w ⬝ᵥ b).re := by
  rw [quaternionForm_vector_add H hH, quaternionForm_inverse_vector H V hHV,
    Matrix.mulVec_mulVec, hHV, Matrix.one_mulVec, real_dot_swap]

theorem current_square_identity {m N : ℕ}
    (H V : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (hH : H.IsHermitian)
    (hHV : H*V=1) (hVH : V*H=1)
    (ρ : Fin N → ℝ) (b : Fin N → Fin m → Quaternion ℝ)
    (hmass : mooreDet m H = ∑ l, ρ l) (w : Fin m → Quaternion ℝ) :
    realTrace ((∑ l, ρ l • outer (b l)) * H) + quaternionForm (mooreCofactor m H) w +
      2 * (star w ⬝ᵥ (∑ l, ρ l • b l)).re =
      ∑ l, ρ l * quaternionForm H (b l+V*ᵥw) := by
  have hstress : realTrace ((∑ l, ρ l • outer (b l)) * H) =
      ∑ l, ρ l * quaternionForm H (b l) := by
    rw [realTrace_mul_comm, Matrix.mul_sum]
    simp only [Matrix.mul_smul, realTrace, Matrix.trace_sum, Matrix.trace_smul,
      quaternion_re_sum, Quaternion.re_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro l _
    rw [← realTrace, realTrace_mul_outer]
  have hflux : (star w ⬝ᵥ (∑ l, ρ l • b l)).re =
      ∑ l, ρ l * (star w ⬝ᵥ b l).re := by
    rw [dotProduct_sum]
    simp only [dotProduct_smul, quaternion_re_sum, Quaternion.re_smul, smul_eq_mul]
  rw [hstress, quaternionForm_cofactor_inverse H V hH hHV hVH, hmass, hflux]
  simp_rw [current_square_term H V hH hHV]
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem current_square_nonneg {m N : ℕ}
    (H V : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (hH : H.IsHermitian)
    (hHV : H*V=1) (hVH : V*H=1)
    (hpos : ∀ v, 0 ≤ quaternionForm H v)
    (ρ : Fin N → ℝ) (hρ : ∀ l, 0 ≤ ρ l) (b : Fin N → Fin m → Quaternion ℝ)
    (hmass : mooreDet m H = ∑ l, ρ l) (w : Fin m → Quaternion ℝ) :
    0 ≤ realTrace ((∑ l, ρ l • outer (b l)) * H) + quaternionForm (mooreCofactor m H) w +
      2 * (star w ⬝ᵥ (∑ l, ρ l • b l)).re := by
  rw [current_square_identity H V hH hHV hVH ρ b hmass w]
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hρ l) (hpos _)

end KakeyaSharp
