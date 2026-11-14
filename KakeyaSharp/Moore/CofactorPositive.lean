/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Moore.Boundary
public import KakeyaSharp.Moore.NullLagrangian
public import KakeyaSharp.Green.GreenAlgebra

@[expose] public section

/-! Positivity of the actual Moore cofactor, including at singular backgrounds. -/
noncomputable section
namespace KakeyaSharp.Moore
open Matrix KakeyaSharp.QuaternionAlgebra
open scoped MatrixOrder ComplexOrder

theorem realTrace_mul_outer {n : ℕ} (C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (z : Fin n → Quaternion ℝ) :
    realTrace (C * outer z) = KakeyaSharp.quaternionForm C z := by
  change realTrace (C * vecMulVec z (star z)) = _
  rw [realTrace_mul_vecMulVec]
  simp only [KakeyaSharp.quaternionForm, dotProduct, Pi.star_apply]

theorem complexify_outer_posSemidef {n : ℕ} (z : Fin n → Quaternion ℝ) :
    (complexify (outer z)).PosSemidef := by
  apply (complexify_posSemidef_iff (outer_isHermitian z)).mpr
  intro w
  rw [KakeyaSharp.quaternionForm_outer]
  exact sq_nonneg _

theorem mooreCofactor_posSemidef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : (complexify A).PosSemidef) :
    (complexify (mooreCofactor n A)).PosSemidef := by
  apply (complexify_posSemidef_iff (mooreCofactor_isHermitian n A)).mpr
  intro z
  rw [← realTrace_mul_outer, mooreCofactor_pairing n A (outer z) (outer_isHermitian z)]
  exact mooreDifferential_nonneg_of_posSemidef A (outer z) hA (complexify_outer_posSemidef z)

theorem mooreCofactor_quaternionForm_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : A.IsHermitian)
    (hpos : ∀ z, 0 ≤ KakeyaSharp.quaternionForm A z) (w : Fin n → Quaternion ℝ) :
    0 ≤ KakeyaSharp.quaternionForm (mooreCofactor n A) w :=
  (complexify_posSemidef_iff (mooreCofactor_isHermitian n A)).mp
    (mooreCofactor_posSemidef A ((complexify_posSemidef_iff hA).mpr hpos)) w

end KakeyaSharp.Moore

namespace KakeyaSharp.Green
open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore

theorem realCoefficients_quadratic {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (e : Fin s → Quaternion ℝ)
    (ξ : Fin n × Fin s → ℝ) :
    (∑ p, ∑ q, realCoefficients e A p q * (ξ p * ξ q)) =
      KakeyaSharp.quaternionForm A (gradientMap e ξ) := by
  let H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ := fun p q => ξ p * ξ q
  have hH : H.IsSymm := by
    ext p q
    exact mul_comm _ _
  have he := realTrace_hessianMap A e H hH
  rw [show hessianMap e H = outer (gradientMap e ξ) from hessianMap_rankOne e ξ,
    realTrace_mul_outer] at he
  exact he.symm

end KakeyaSharp.Green

