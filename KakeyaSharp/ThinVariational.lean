/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinSource

@[expose] public section

/-! Optimizing the amplitude gives a logarithmic variational lower bound. -/

noncomputable section
open MeasureTheory Set Metric
namespace KakeyaSharp

def thinAmplitudeCoefficient (m : ℕ) : ℝ :=
  min 1 (thinCoreConstant m / (2 * thinEnergyConstant m))

def thinLowerConstant (m : ℕ) : ℝ :=
  thinAmplitudeCoefficient m * thinCoreConstant m / 2

theorem thinAmplitudeCoefficient_pos (m : ℕ) : 0 < thinAmplitudeCoefficient m := by
  unfold thinAmplitudeCoefficient
  exact lt_min (by norm_num) (div_pos (thinCoreConstant_pos m)
    (mul_pos (by norm_num) (thinEnergyConstant_pos m)))

theorem thinLowerConstant_pos (m : ℕ) : 0 < thinLowerConstant m := by
  unfold thinLowerConstant
  exact div_pos (mul_pos (thinAmplitudeCoefficient_pos m) (thinCoreConstant_pos m)) (by norm_num)

theorem thinAmplitudeCoefficient_bound {m : ℕ} (hm : 1 ≤ m) :
    thinAmplitudeCoefficient m ^ m * thinEnergyConstant m / ((m : ℝ) + 1) ≤
      thinCoreConstant m / 2 := by
  have ht0 := (thinAmplitudeCoefficient_pos m).le
  have ht1 : thinAmplitudeCoefficient m ≤ 1 := min_le_left _ _
  have htm : thinAmplitudeCoefficient m ^ m ≤ thinAmplitudeCoefficient m := by
    calc
      _ = thinAmplitudeCoefficient m ^ (m - 1) * thinAmplitudeCoefficient m := by
        rw [← pow_succ, Nat.sub_add_cancel hm]
      _ ≤ _ := mul_le_of_le_one_left ht0 (pow_le_one₀ ht0 ht1)
  have hc := (thinEnergyConstant_pos m).le
  calc
    _ ≤ thinAmplitudeCoefficient m ^ m * thinEnergyConstant m :=
      div_le_self (mul_nonneg (pow_nonneg ht0 _) hc) (by linarith [Nat.cast_nonneg (α := ℝ) m])
    _ ≤ thinAmplitudeCoefficient m * thinEnergyConstant m :=
      mul_le_mul_of_nonneg_right htm hc
    _ ≤ thinCoreConstant m / 2 := by
      change min 1 (thinCoreConstant m / (2 * thinEnergyConstant m)) *
        thinEnergyConstant m ≤ _
      apply (mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ)
        (thinCoreConstant m / (2 * thinEnergyConstant m))) hc).trans_eq
      field_simp [(thinEnergyConstant_pos m).ne']

theorem thinFunctional_lower {m : ℕ} (hm : 1 ≤ m) {η a A : ℝ}
    (hη : 0 < η) (hη10 : η ≤ 1 / 10) (hA : 0 ≤ A)
    {μ : ThinSpace m → ℝ} (hμ : ContinuousOn μ (thinClosedBall m))
    (hμ0 : ∀ z ∈ thinBall m, 0 ≤ μ z)
    (hμa : ∀ z ∈ thinCore m η, a ≤ μ z) :
    (A * thinCoreConstant m * η ^ (2 * m) * a -
      A ^ (m + 1) * thinEnergyConstant m / ((m : ℝ) + 1)) * Real.log (1 / η) ≤
      thinFunctional μ (A • thinProfile η) := by
  rw [thinFunctional_smul]
  have hS := mul_le_mul_of_nonneg_left (thinSource_integral_lower hη hη10 hμ hμ0 hμa) hA
  have hE := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (thinEnergy_le_log hm hη hη10) (pow_nonneg hA (m + 1)))
    (show 0 ≤ (m : ℝ) + 1 by positivity)
  have hh := sub_le_sub hS hE
  convert hh using 1
  · ring
  · rfl

theorem thinSource_test_power {m : ℕ} (hm : 1 ≤ m) {η b : ℝ}
    (hη : 0 < η) (hη10 : η ≤ 1 / 10) (hb : 0 ≤ b)
    {μ : ThinSpace m → ℝ} (hμ : ContinuousOn μ (thinClosedBall m))
    (hμ0 : ∀ z ∈ thinBall m, 0 ≤ μ z)
    (hμb : ∀ z ∈ thinCore m η, b ^ m ≤ μ z) :
    ∃ v : ThinSpace m → ℝ, ThinAdmissible v ∧
      thinLowerConstant m * b ^ (m + 1) * η ^ (2 * m + 2) * Real.log (1 / η) ≤
        thinFunctional μ v := by
  let t := thinAmplitudeCoefficient m
  let A := t * b * η ^ 2
  have ht : 0 ≤ t := (thinAmplitudeCoefficient_pos m).le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A • thinProfile η, (thinProfile_admissible hη).smul hA, ?_⟩
  apply le_trans _ (thinFunctional_lower hm hη hη10 hA hμ hμ0 hμb)
  have hcoeff := thinAmplitudeCoefficient_bound (show 1 ≤ m by omega)
  have hl : 0 ≤ Real.log (1 / η) :=
    Real.log_nonneg ((le_div_iff₀ hη).mpr (by linarith))
  have hh := mul_le_mul_of_nonneg_left
    (show thinCoreConstant m / 2 ≤ thinCoreConstant m -
      t ^ m * thinEnergyConstant m / ((m : ℝ) + 1) by dsimp [t]; linarith)
    (show 0 ≤ t * b ^ (m + 1) * η ^ (2 * m + 2) * Real.log (1 / η) by positivity)
  convert hh using 1
  · dsimp [thinLowerConstant, t]
    ring
  · dsimp [A]
    rw [mul_pow, mul_pow, pow_succ t m, pow_succ b m,
      ← pow_mul, show 2 * (m + 1) = 2 * m + 2 by omega, pow_add η (2 * m) 2]
    ring

/-- The unit-ball thin-source bound, stated with the endpoint exponent. -/
theorem thinSource_variational_lower {m : ℕ} (hm : 1 ≤ m) {η a : ℝ}
    (hη : 0 < η) (hη10 : η ≤ 1 / 10) (ha : 0 ≤ a)
    {μ : ThinSpace m → ℝ} (hμ : ContinuousOn μ (thinClosedBall m))
    (hμ0 : ∀ z ∈ thinBall m, 0 ≤ μ z)
    (hμa : ∀ z ∈ thinCore m η, a ≤ μ z) :
    ∃ v : ThinSpace m → ℝ, ThinAdmissible v ∧
      thinLowerConstant m * a ^ (((m : ℝ) + 1) / m) *
        η ^ (2 * m + 2) * Real.log (1 / η) ≤ thinFunctional μ v := by
  have hm0 : m ≠ 0 := by omega
  let b : ℝ := a ^ ((m : ℝ)⁻¹)
  have hb : 0 ≤ b := Real.rpow_nonneg ha _
  have hbm : b ^ m = a := Real.rpow_inv_natCast_pow ha hm0
  have hbp : b ^ (m + 1) = a ^ (((m : ℝ) + 1) / m) := by
    dsimp [b]
    rw [← Real.rpow_mul_natCast ha]
    congr 1
    push_cast
    ring
  obtain ⟨v, hv, hl⟩ := thinSource_test_power hm hη hη10 hb hμ hμ0
    (fun z hz => by rw [hbm]; exact hμa z hz)
  exact ⟨v, hv, by simpa only [hbp] using hl⟩

end KakeyaSharp
