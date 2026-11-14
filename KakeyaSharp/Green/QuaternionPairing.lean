/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.DirectionalCofactor

@[expose] public section

/-! The full quaternionic pairing, including the imaginary components which
are needed for cancellation between different parameter directions. -/
noncomputable section
namespace KakeyaSharp.Green
open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped Matrix.Norms.Elementwise

def quaternionPairing {n : ℕ} (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (u v : Fin n → Quaternion ℝ) : Quaternion ℝ :=
  ∑ i, ∑ j, star (u i) * A i j * v j

def quaternionCoefficients {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (p q : Fin n × Fin s) : Quaternion ℝ :=
  star (e p.2) * A p.1 q.1 * e q.2

theorem quaternionCoefficients_star {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {A : Matrix (Fin n) (Fin n) (Quaternion ℝ)} (hA : A.IsHermitian)
    (p q : Fin n × Fin s) :
    star (quaternionCoefficients e A q p) = quaternionCoefficients e A p q := by
  simp only [quaternionCoefficients, star_mul, star_star, hA.apply, mul_assoc]

theorem quaternionPairing_gradient {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (ξ η : Fin n × Fin s → ℝ) :
    quaternionPairing A (gradientMap e ξ) (gradientMap e η) =
      ∑ p, ∑ q, (ξ p * η q) • quaternionCoefficients e A p q := by
  simp only [quaternionPairing, gradientMap, star_sum, Quaternion.star_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul, quaternionCoefficients, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, ∑ β, ∑ α, (η (j,β) * ξ (i,α)) • (star (e α) * A i j * e β)) =
        ∑ j, ∑ α, ∑ β, (ξ (i,α) * η (j,β)) • (star (e α) * A i j * e β) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      rw [mul_comm (η (j,β)) (ξ (i,α))]
    _ = _ := Finset.sum_comm

theorem quaternion_hessian_contraction {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {A : Matrix (Fin n) (Fin n) (Quaternion ℝ)} (hA : A.IsHermitian)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) (hH : H.IsSymm) :
    (∑ p, ∑ q, H p q • quaternionCoefficients e A p q) =
      (realTrace (A * hessianMap e H) : Quaternion ℝ) := by
  let q : Quaternion ℝ := ∑ p, ∑ q, H p q • quaternionCoefficients e A p q
  have hq : star q = q := by
    dsimp only [q]
    simp only [star_sum, Quaternion.star_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro r _
    rw [quaternionCoefficients_star e hA, hH.apply]
  have hre : q.re = realTrace (A * hessianMap e H) := by
    dsimp only [q]
    simp only [quaternion_re_sum, Quaternion.re_smul, smul_eq_mul]
    rw [realTrace_hessianMap A e H hH]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro r _
    exact mul_comm _ _
  change q = _
  rw [(Quaternion.star_eq_self.mp hq), hre]

def quaternionCoefficientLinear {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (p q : Fin n × Fin s) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →ₗ[ℝ] Quaternion ℝ where
  toFun A := quaternionCoefficients e A p q
  map_add' A B := by simp [quaternionCoefficients, mul_add, add_mul]
  map_smul' c A := by simp [quaternionCoefficients]

def testedCoefficientCLM {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (L : Quaternion ℝ →L[ℝ] ℝ) (p q : Fin n × Fin s) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →L[ℝ] ℝ :=
  L.comp (quaternionCoefficientLinear e p q).toContinuousLinearMap

theorem testedCoefficientCLM_apply {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (L : Quaternion ℝ →L[ℝ] ℝ) (p q : Fin n × Fin s)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    testedCoefficientCLM e L p q A = L (quaternionCoefficients e A p q) := rfl

theorem testedCoefficients_divergence_zero {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (L : Quaternion ℝ →L[ℝ] ℝ)
    (dA : Fin n × Fin s → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hd : ∀ j, strongDivergence e dA j = 0) (q : Fin n × Fin s) :
    (∑ p, testedCoefficientCLM e L p q (dA p)) = 0 := by
  simp only [testedCoefficientCLM_apply, ← map_sum]
  have he : (∑ p, quaternionCoefficients e (dA p) p q) =
      strongDivergence e dA q.1 * e q.2 := by
    simp only [quaternionCoefficients, strongDivergence, Fintype.sum_prod_type, Finset.sum_mul]
  rw [he, hd, zero_mul, map_zero]

theorem tested_hessian_contraction {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (L : Quaternion ℝ →L[ℝ] ℝ)
    {A : Matrix (Fin n) (Fin n) (Quaternion ℝ)} (hA : A.IsHermitian)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) (hH : H.IsSymm) :
    (∑ p, ∑ q, testedCoefficientCLM e L p q A * H p q) =
      realTrace (A * hessianMap e H) * L 1 := by
  have h := congrArg L (quaternion_hessian_contraction e hA H hH)
  have hr (a : ℝ) : L (a : Quaternion ℝ) = a * L 1 := by
    rw [show (a : Quaternion ℝ) = a • (1 : Quaternion ℝ) by ext <;> simp,
      map_smul, smul_eq_mul]
  simp only [map_sum, map_smul, smul_eq_mul, hr] at h
  simpa only [testedCoefficientCLM_apply, mul_comm] using h

theorem tested_pairing_gradient {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (L : Quaternion ℝ →L[ℝ] ℝ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (ξ η : Fin n × Fin s → ℝ) :
    L (quaternionPairing A (gradientMap e ξ) (gradientMap e η)) =
      ∑ p, ∑ q, testedCoefficientCLM e L p q A * ξ p * η q := by
  rw [quaternionPairing_gradient]
  simp only [map_sum, map_smul, smul_eq_mul, testedCoefficientCLM_apply]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

def quaternionSandwichLinear (a b : Quaternion ℝ) : Quaternion ℝ →ₗ[ℝ] ℝ where
  toFun q := (a*q*b).re
  map_add' q r := by simp [mul_add, add_mul]
  map_smul' c q := by simp

def quaternionSandwichCLM (a b : Quaternion ℝ) : Quaternion ℝ →L[ℝ] ℝ :=
  (quaternionSandwichLinear a b).toContinuousLinearMap

theorem quaternionSandwichCLM_apply (a b q : Quaternion ℝ) :
    quaternionSandwichCLM a b q = (a*q*b).re := rfl

theorem quaternionPairing_re {n : ℕ} (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (u : Fin n → Quaternion ℝ) : (quaternionPairing A u u).re = KakeyaSharp.quaternionForm A u := by
  simp only [quaternionPairing, KakeyaSharp.quaternionForm, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_assoc]

theorem quaternionPairing_sum_left {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (u : Fin k → Fin n → Quaternion ℝ) (v : Fin n → Quaternion ℝ) :
    quaternionPairing A (fun i => ∑ a, u a i) v = ∑ a, quaternionPairing A (u a) v := by
  simp only [quaternionPairing, star_sum, Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ a, star (u a i) * A i j * v j) =
        ∑ i, ∑ a, ∑ j, star (u a i) * A i j * v j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem quaternionPairing_sum_right {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (u : Fin n → Quaternion ℝ) (v : Fin k → Fin n → Quaternion ℝ) :
    quaternionPairing A u (fun i => ∑ a, v a i) = ∑ a, quaternionPairing A u (v a) := by
  simp only [quaternionPairing, Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ a, star (u i) * A i j * v a j) =
        ∑ i, ∑ a, ∑ j, star (u i) * A i j * v a j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem quaternionPairing_right_mul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (u v : Fin n → Quaternion ℝ) (a b : Quaternion ℝ) :
    quaternionPairing A (fun i => u i*a) (fun i => v i*b) =
      star a * quaternionPairing A u v * b := by
  simp only [quaternionPairing, star_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem quaternionForm_sum_right_mul {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (u : Fin k → Fin n → Quaternion ℝ) (e : Fin k → Quaternion ℝ) :
    KakeyaSharp.quaternionForm A (fun i => ∑ a, u a i * star (e a)) =
      ∑ a, ∑ b, (e a * quaternionPairing A (u a) (u b) * star (e b)).re := by
  rw [← quaternionPairing_re, quaternionPairing_sum_left]
  simp_rw [quaternionPairing_sum_right, quaternionPairing_right_mul, star_star, quaternion_re_sum]

end KakeyaSharp.Green
