/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Moore.Form
public import KakeyaSharp.Moore.Outer

@[expose] public section

/-! A positive quaternionic matrix has a genuine two-sided quaternionic inverse. -/

noncomputable section

namespace KakeyaSharp.Moore

open Matrix
open scoped MatrixOrder ComplexOrder

theorem quaternionForm_eq_dotProduct {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (z : Fin n → Quaternion ℝ) :
    KakeyaSharp.quaternionForm A z = (star z ⬝ᵥ A *ᵥ z).re := by
  simp only [KakeyaSharp.quaternionForm, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]

theorem quaternionMulVec_injective_of_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hpos : ∀ z ≠ 0, 0 < KakeyaSharp.quaternionForm A z) : Function.Injective A.mulVec := by
  change Function.Injective (quaternionMulVecLinear A)
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  by_contra hne
  have hp := hpos z hne
  have hz' : A *ᵥ z = 0 := hz
  rw [quaternionForm_eq_dotProduct, hz'] at hp
  simp at hp

/-- The inverse is constructed from surjectivity of real-linear multiplication;
no commutative determinant or quaternionic spectral theorem is assumed. -/
theorem exists_quaternion_inverse_of_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hpos : ∀ z ≠ 0, 0 < KakeyaSharp.quaternionForm A z) :
    ∃ C : Matrix (Fin n) (Fin n) (Quaternion ℝ), A * C = 1 ∧ C * A = 1 := by
  have hi := quaternionMulVec_injective_of_pos A hpos
  have hs : Function.Surjective (quaternionMulVecLinear A) :=
    LinearMap.surjective_of_injective hi
  choose v hv using hs
  let C : Matrix (Fin n) (Fin n) (Quaternion ℝ) := fun i j ↦ v (Pi.single j 1) i
  have hAC : A * C = 1 := by
    apply Matrix.ext
    intro i j
    have h := congrFun (hv (Pi.single j 1)) i
    change (A *ᵥ v (Pi.single j 1)) i = (Pi.single j (1 : Quaternion ℝ) : Fin n → Quaternion ℝ) i at h
    change (A *ᵥ v (Pi.single j 1)) i = (1 : Matrix _ _ _) i j
    simpa only [Matrix.one_apply, Pi.single_apply, eq_comm] using h
  refine ⟨C, hAC, ?_⟩
  have he : A * (C * A) = A * 1 := by rw [← Matrix.mul_assoc, hAC, one_mul, mul_one]
  apply Matrix.ext
  intro i j
  apply congrFun (hi (a₁ := fun k ↦ (C * A) k j) (a₂ := fun k ↦ (1 : Matrix _ _ _) k j) ?_) i
  funext k
  exact congrFun (congrFun he k) j

theorem exists_quaternion_inverse_of_complexify_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : (complexify A).PosDef) :
    ∃ C : Matrix (Fin n) (Fin n) (Quaternion ℝ), A * C = 1 ∧ C * A = 1 :=
  exists_quaternion_inverse_of_pos A
    ((complexify_posDef_iff (isHermitian_of_complexify hA.isHermitian)).mp hA)

end KakeyaSharp.Moore

