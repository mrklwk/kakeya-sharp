/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Moore.ScalarOuter

@[expose] public section

/-! A genuine quaternionic Hermitian cofactor matrix representing the first
variation. -/

noncomputable section

namespace KakeyaSharp.Moore

open Matrix KakeyaSharp.QuaternionAlgebra

def quaternionDualVector (L : Quaternion ℝ →ₗ[ℝ] ℝ) : Quaternion ℝ :=
  ⟨L 1, L ⟨0, 1, 0, 0⟩, L ⟨0, 0, 1, 0⟩, L ⟨0, 0, 0, 1⟩⟩

theorem quaternionDualVector_apply (L : Quaternion ℝ →ₗ[ℝ] ℝ) (q : Quaternion ℝ) :
    (star (quaternionDualVector L) * q).re = L q := by
  have hq : q = q.re • (1 : Quaternion ℝ) + q.imI • ⟨0, 1, 0, 0⟩ +
      q.imJ • ⟨0, 0, 1, 0⟩ + q.imK • ⟨0, 0, 0, 1⟩ := by
    ext <;> simp
  have hL : L q = q.re * L 1 + q.imI * L ⟨0, 1, 0, 0⟩ +
      q.imJ * L ⟨0, 0, 1, 0⟩ + q.imK * L ⟨0, 0, 0, 1⟩ := by
    conv_lhs => rw [hq]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hL]
  simp [quaternionDualVector]
  ring

def quaternionEntryLinear {n : ℕ} (i j : Fin n) :
    Quaternion ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) (Quaternion ℝ) where
  toFun := Matrix.single i j
  map_add' := Matrix.single_add i j
  map_smul' := fun c q ↦ (Matrix.smul_single c i j q).symm

def mooreDifferentialLinear (n : ℕ) (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →ₗ[ℝ] ℝ where
  toFun := mooreDifferential n A
  map_add' := mooreDifferential_add n A
  map_smul' := fun c D ↦ mooreDifferential_smul n c A D

def rawCofactor (n : ℕ) (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
  fun i j ↦ star (quaternionDualVector ((mooreDifferentialLinear n A).comp
    (quaternionEntryLinear j i)))

def realTrace {n : ℕ} (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) : ℝ := A.trace.re

theorem quaternion_re_sum {ι : Type*} (s : Finset ι) (f : ι → Quaternion ℝ) :
    (s.sum f).re = s.sum (fun i ↦ (f i).re) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem realTrace_mul_comm {n : ℕ} (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    realTrace (A * B) = realTrace (B * A) := by
  change (∑ i, (A * B) i i).re = (∑ i, (B * A) i i).re
  simpa only [quaternion_re_sum] using quaternionRealTrace_mul_comm n A B

theorem realTrace_conjTranspose {n : ℕ} (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    realTrace Aᴴ = realTrace A := by
  simp [realTrace, Matrix.trace_conjTranspose]

theorem realTrace_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    realTrace (A + B) = realTrace A + realTrace B := by simp [realTrace]

theorem realTrace_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    realTrace (c • A) = c * realTrace A := by simp [realTrace]

theorem rawCofactor_pairing (n : ℕ) (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    realTrace (rawCofactor n A * D) = mooreDifferential n A D := by
  change (∑ i, (rawCofactor n A * D) i i).re = mooreDifferentialLinear n A D
  conv_rhs => rw [Matrix.matrix_eq_sum_single D]
  simp only [map_sum, quaternion_re_sum, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact quaternionDualVector_apply ((mooreDifferentialLinear n A).comp (quaternionEntryLinear i j))
    (D i j)

/-- The Hermitian cofactor, defined without invertibility and with the usual
real-trace normalization of the Moore determinant's differential. -/
def mooreCofactor (n : ℕ) (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
  (1 / 2 : ℝ) • (rawCofactor n A + (rawCofactor n A)ᴴ)

theorem mooreCofactor_isHermitian (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) : (mooreCofactor n A).IsHermitian := by
  rw [Matrix.IsHermitian, mooreCofactor, quaternionMatrix_conjTranspose_real_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]

theorem realTrace_star_left {n : ℕ} (C D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : D.IsHermitian) : realTrace (Cᴴ * D) = realTrace (C * D) := by
  have hDe : Dᴴ = D := hD
  calc
    realTrace (Cᴴ * D) = realTrace (D * C)ᴴ := by rw [Matrix.conjTranspose_mul, hDe]
    _ = realTrace (D * C) := realTrace_conjTranspose _
    _ = realTrace (C * D) := realTrace_mul_comm _ _

theorem mooreCofactor_pairing (n : ℕ) (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : D.IsHermitian) : realTrace (mooreCofactor n A * D) = mooreDifferential n A D := by
  rw [mooreCofactor, Matrix.smul_mul, Matrix.add_mul, realTrace_smul, realTrace_add,
    realTrace_star_left _ _ hD, rawCofactor_pairing]
  ring

theorem quaternion_re_mul_comm (p q : Quaternion ℝ) : (p * q).re = (q * p).re := by
  simp only [Quaternion.re_mul]
  ring

theorem realTrace_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    realTrace (A - B) = realTrace A - realTrace B := by simp [realTrace]

theorem mooreCofactor_euler {n : ℕ} (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : A.IsHermitian) : realTrace (mooreCofactor n A * A) = (n : ℝ) * mooreDet n A := by
  rw [mooreCofactor_pairing n A A hA, mooreDifferential_self]

end KakeyaSharp.Moore

