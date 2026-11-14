/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Moore.Cofactor

@[expose] public section

/-! Real coefficient contractions for the quaternionic Green identities. -/

noncomputable section
namespace KakeyaSharp.Green

open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped Matrix.Norms.Elementwise

theorem quaternion_re_triple_cycle (p q r : Quaternion ℝ) :
    (p * (q * r)).re = (r * p * q).re := by
  rw [← mul_assoc, KakeyaSharp.Moore.quaternion_re_mul_comm]
  rw [mul_assoc]

theorem realTrace_hessianMap_transpose {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (e : Fin s → Quaternion ℝ)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) :
    KakeyaSharp.Moore.realTrace (A * KakeyaSharp.QuaternionAlgebra.hessianMap e H) =
      ∑ p, ∑ q, KakeyaSharp.QuaternionAlgebra.realCoefficients e A p q * H q p := by
  simp only [KakeyaSharp.Moore.realTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply, KakeyaSharp.QuaternionAlgebra.hessianMap,
    Finset.mul_sum, mul_smul_comm, KakeyaSharp.Moore.quaternion_re_sum, Quaternion.re_smul,
    KakeyaSharp.QuaternionAlgebra.realCoefficients, Fintype.sum_prod_type, quaternion_re_triple_cycle]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, ∑ α, ∑ β, H (j, α) (i, β) * (star (e β) * A i j * e α).re) =
        ∑ j, ∑ β, ∑ α, H (j, α) (i, β) * (star (e β) * A i j * e α).re := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ β, ∑ j, ∑ α, H (j, α) (i, β) * (star (e β) * A i j * e α).re :=
      Finset.sum_comm
    _ = _ := by simp_rw [mul_comm]

theorem realTrace_hessianMap {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (e : Fin s → Quaternion ℝ)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) (hH : H.IsSymm) :
    KakeyaSharp.Moore.realTrace (A * KakeyaSharp.QuaternionAlgebra.hessianMap e H) =
      ∑ p, ∑ q, KakeyaSharp.QuaternionAlgebra.realCoefficients e A p q * H p q := by
  rw [realTrace_hessianMap_transpose]
  have he (p q : Fin n × Fin s) : H q p = H p q := congrFun (congrFun hH p) q
  simp_rw [he]

def realCoefficientLinear {n s : ℕ} (e : Fin s → Quaternion ℝ) (p q : Fin n × Fin s) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →ₗ[ℝ] ℝ where
  toFun := fun A ↦ KakeyaSharp.QuaternionAlgebra.realCoefficients e A p q
  map_add' A B := by simp [KakeyaSharp.QuaternionAlgebra.realCoefficients, mul_add, add_mul]
  map_smul' c A := by simp [KakeyaSharp.QuaternionAlgebra.realCoefficients]

def realCoefficientCLM {n s : ℕ} (e : Fin s → Quaternion ℝ) (p q : Fin n × Fin s) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →L[ℝ] ℝ :=
  (realCoefficientLinear e p q).toContinuousLinearMap

end KakeyaSharp.Green

