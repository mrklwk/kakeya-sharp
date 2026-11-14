/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinEnergy

@[expose] public section

/-! Amplitude scaling and admissibility for the actual variational functional. -/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff
namespace KakeyaSharp
open KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore

def determinantEnergy {m : ℕ} (f : ThinSpace m → ℝ) : ℝ :=
  ∫ z in thinBall m, (-f z) * mooreDet m (thinQuaternionHessian f z)

def thinFunctional {m : ℕ} (μ f : ThinSpace m → ℝ) : ℝ :=
  (∫ z in thinBall m, (-f z) * μ z) - determinantEnergy f / ((m : ℝ) + 1)

def ThinAdmissible {m : ℕ} (f : ThinSpace m → ℝ) : Prop :=
  (∀ z ∈ thinClosedBall m, ContDiffAt ℝ 3 f z) ∧
  (∀ z : ThinSpace m, ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 = 1 → f z = 0) ∧
  (∀ z ∈ thinClosedBall m, ∀ w : Fin m → Quaternion ℝ,
    0 ≤ quaternionForm (thinQuaternionHessian f z) w)

theorem thinQuaternionHessian_smul {m : ℕ} (c : ℝ) (f : ThinSpace m → ℝ)
    (z : ThinSpace m) :
    thinQuaternionHessian (c • f) z = c • thinQuaternionHessian f z := by
  have hh : thinRealHessian (c • f) z = c • thinRealHessian f z := by
    ext i j
    change fderiv ℝ (fderiv ℝ (c • f)) z (thinDirection i.1 i.2)
      (thinDirection j.1 j.2) =
      c * (fderiv ℝ (fderiv ℝ f) z (thinDirection i.1 i.2) (thinDirection j.1 j.2))
    rw [fderiv_const_smul_field (𝕜 := ℝ) (f := f) c,
      fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ f) c]
    rfl
  unfold thinQuaternionHessian
  rw [hh, hessianMap_smul]

theorem determinantEnergy_smul {m : ℕ} (c : ℝ) (f : ThinSpace m → ℝ) :
    determinantEnergy (c • f) = c ^ (m + 1) * determinantEnergy f := by
  unfold determinantEnergy
  simp_rw [thinQuaternionHessian_smul, mooreDet_smul, Pi.smul_apply, smul_eq_mul]
  have he (z : ThinSpace m) : -(c * f z) * (c ^ m *
      mooreDet m (thinQuaternionHessian f z)) =
      c ^ (m + 1) * ((-f z) * mooreDet m (thinQuaternionHessian f z)) := by
    rw [pow_succ]
    ring
  simp_rw [he]
  exact integral_const_mul _ _

theorem thinProfile_admissible {m : ℕ} {η : ℝ} (hη : 0 < η) :
    ThinAdmissible (thinProfile η : ThinSpace m → ℝ) := by
  refine ⟨fun _ hz => (thinProfile_smooth hη hz).of_le (by simp),
    fun _ hz => thinProfile_boundary hη hz, ?_⟩
  intro z hz w
  by_cases hw : w = 0
  · subst w
    simp [quaternionForm]
  · exact (thinProfile_quaternionHessian_positive hη hz hw).le

theorem ThinAdmissible.smul {m : ℕ} {f : ThinSpace m → ℝ} (hf : ThinAdmissible f)
    {c : ℝ} (hc : 0 ≤ c) : ThinAdmissible (c • f) := by
  refine ⟨fun z hz => contDiffAt_const.smul (hf.1 z hz), ?_, ?_⟩
  · intro z hz
    simp [hf.2.1 z hz]
  · intro z hz w
    rw [thinQuaternionHessian_smul, quaternionForm_smul]
    exact mul_nonneg hc (hf.2.2 z hz w)

theorem thinFunctional_smul {m : ℕ} (c : ℝ) (μ f : ThinSpace m → ℝ) :
    thinFunctional μ (c • f) = c * (∫ z in thinBall m, (-f z) * μ z) -
      c ^ (m + 1) * determinantEnergy f / ((m : ℝ) + 1) := by
  unfold thinFunctional
  rw [determinantEnergy_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, neg_mul_eq_mul_neg, mul_assoc, integral_const_mul]

theorem thinProfile_scaled_energy {m : ℕ} (hm : 1 ≤ m) {η c : ℝ}
    (hη : 0 < η) (hη10 : η ≤ 1 / 10) (hc : 0 ≤ c) :
    determinantEnergy (c • (thinProfile η : ThinSpace m → ℝ)) ≤
      c ^ (m + 1) * thinEnergyConstant m * Real.log (1 / η) := by
  rw [determinantEnergy_smul]
  exact (mul_le_mul_of_nonneg_left (thinEnergy_le_log hm hη hη10)
    (pow_nonneg hc _)).trans_eq (by ring)

end KakeyaSharp
