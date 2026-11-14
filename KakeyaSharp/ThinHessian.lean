/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.HessianCalculus

@[expose] public section

/-! The quaternionic Hessian of the logarithmic test, in the actual three
real coordinate directions of each quaternionic index. -/

noncomputable section
namespace KakeyaSharp
open KakeyaSharp.QuaternionAlgebra

def thinDirection {m : ℕ} (i : Fin m) : Fin 3 → ThinSpace m :=
  ![(EuclideanSpace.single i 1, 0),
    (0, EuclideanSpace.single (i, 0) 1),
    (0, EuclideanSpace.single (i, 1) 1)]

def thinRealHessian {m : ℕ} (f : ThinSpace m → ℝ) (z : ThinSpace m) :
    Matrix (Fin m × Fin 3) (Fin m × Fin 3) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ f) z (thinDirection i.1 i.2) (thinDirection j.1 j.2)

def thinQuaternionHessian {m : ℕ} (f : ThinSpace m → ℝ) (z : ThinSpace m) :
    Matrix (Fin m) (Fin m) (Quaternion ℝ) :=
  hessianMap threeSlots (thinRealHessian f z)

/-- The vector `G(|P|²)`, with its two imaginary components displayed. -/
def thinPGradient {m : ℕ} (z : ThinSpace m) (i : Fin m) : Quaternion ℝ :=
  ⟨0, 2 * z.2 (i, 0), 2 * z.2 (i, 1), 0⟩

def thinXVector {m : ℕ} (z : ThinSpace m) (i : Fin m) : Quaternion ℝ :=
  (z.1 i : Quaternion ℝ)

theorem thinPGradient_norm_sq {m : ℕ} (z : ThinSpace m) :
    (∑ i, ‖thinPGradient z i‖ ^ 2) = 4 * ‖z.2‖ ^ 2 := by
  have hn (q : Quaternion ℝ) : ‖q‖ ^ 2 = Quaternion.normSq q := by
    rw [Quaternion.normSq_eq_norm_mul_self, pow_two]
  simp_rw [hn, Quaternion.normSq_def']
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [thinPGradient]
  ring

/-- The manuscript's displayed Hessian is derived from Fréchet derivatives. -/
theorem thinProfile_quaternionHessian {m : ℕ} {η : ℝ} (hη : 0 < η)
    {z : ThinSpace m} (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) :
    thinQuaternionHessian (thinProfile η) z =
      (4 / thinNumerator η z) • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) -
      (1 / thinNumerator η z ^ 2) • outer (thinPGradient z) +
      (2 / thinDenominator η z) • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) +
      (4 / thinDenominator η z ^ 2) • outer (thinXVector z) := by
  apply Matrix.ext
  intro i j
  simp only [thinQuaternionHessian, hessianMap, thinRealHessian,
    thinProfile_hessian hη hz, Fin.sum_univ_three]
  by_cases hij : i = j
  · subst j
    ext <;> simp [thinDirection, threeSlots, thinPGradient, thinXVector, outer,
      EuclideanSpace.inner_single_right] <;> ring
  · ext <;> simp [thinDirection, threeSlots, thinPGradient, thinXVector, outer,
      EuclideanSpace.inner_single_right, hij, Ne.symm hij] <;> ring

end KakeyaSharp
