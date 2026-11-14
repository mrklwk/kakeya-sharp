/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Duality
public import KakeyaSharp.Measurability

@[expose] public section

/- Adapted from openai/math, Apache-2.0, retrieved 2026-11-12.
Namespace and imports changed to isolate the elementary Kakeya infrastructure.
See SOURCES.json and LICENSE-OpenAI for provenance. -/
open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace KakeyaSharp

theorem ennreal_rpow_iSup {ι : Type*} (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, f i ^ p :=
  (ENNReal.orderIsoRpow p hp).map_iSup f

/-- Each direction has its own independently chosen tube center. -/
theorem finite_power_sup_le {m : ℕ} {X : Type*} [Nonempty X]
    (F : Fin m → X → ℝ≥0∞) {p : ℝ} (hp : 0 < p) {B : ℝ≥0∞}
    (h : ∀ x : Fin m → X, ∑ i, F i (x i) ^ p ≤ B) :
    ∑ i, (⨆ x, F i x) ^ p ≤ B := by
  simp_rw [ennreal_rpow_iSup _ hp]
  rw [finsetSum_iSup_independent]
  exact iSup_le h

theorem normalized_finite_moment_le {m : ℕ} (I : Fin m → ℝ)
    (J : Fin m → ℝ≥0∞) {p k B : ℝ} (hp : 0 < p) (hk : 0 < k)
    (hB : 0 ≤ B) (hI : ∀ i, 0 ≤ I i)
    (hJ : ∀ i, J i ≤ ENNReal.ofReal (I i / k))
    (hbound : (∑ i, I i ^ p) ^ (1 / p) ≤ B) :
    ∑ i, J i ^ p ≤ ENNReal.ofReal ((B / k) ^ p) := by
  have hsum : 0 ≤ ∑ i, I i ^ p := Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hI i) _
  have hs : ∑ i, I i ^ p ≤ B ^ p := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hsum _) hbound hp.le
    simpa only [← Real.rpow_mul hsum, one_div_mul_cancel hp.ne', Real.rpow_one] using h
  calc
    ∑ i, J i ^ p ≤ ∑ i, ENNReal.ofReal ((I i / k) ^ p) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hI i) hk.le) hp.le]
      exact ENNReal.rpow_le_rpow (hJ i) hp.le
    _ = ENNReal.ofReal ((∑ i, I i ^ p) / k ^ p) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
        Real.rpow_nonneg (div_nonneg (hI i) hk.le) _)]
      congr 1
      simp_rw [Real.div_rpow (hI _) hk.le]
      rw [Finset.sum_div]
    _ ≤ ENNReal.ofReal (B ^ p / k ^ p) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hs (Real.rpow_nonneg hk.le _))
    _ = ENNReal.ofReal ((B / k) ^ p) := by rw [Real.div_rpow hB hk.le]

/-- A uniform vector bound for tube integrals controls the actual supremum
over all centers, without any attainment or countability assumption. -/
theorem finite_kakeya_moment_of_integral_bound {n m : ℕ} {δ p k B : ℝ}
    (hp : 1 ≤ p) (hk : 0 < k) (hB : 0 ≤ B) (v : Fin m → Space n)
    (f : Space n → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hvol : ∀ i x, ENNReal.ofReal k ≤ volume (KakeyaSharp.tube δ (v i) x))
    (hbound : ∀ x : Fin m → Space n,
      (∑ i, (∫ y in KakeyaSharp.tube δ (v i) (x i), ‖f y‖) ^ p) ^ (1 / p) ≤ B) :
    ∑ i, KakeyaSharp.kakeyaMaximal δ f (v i) ^ p ≤ ENNReal.ofReal ((B / k) ^ p) := by
  apply finite_power_sup_le (fun i x ↦ tubeMass δ f (v i) x / volume (KakeyaSharp.tube δ (v i) x))
    (by linarith : 0 < p)
  intro x
  apply normalized_finite_moment_le
    (fun i ↦ ∫ y in KakeyaSharp.tube δ (v i) (x i), ‖f y‖)
    (fun i ↦ tubeMass δ f (v i) (x i) / volume (KakeyaSharp.tube δ (v i) (x i)))
    (by linarith) hk hB (fun i ↦ integral_nonneg fun y ↦ norm_nonneg (f y))
    _ (hbound x)
  intro i
  have hfin : IsFiniteMeasure (volume.restrict (KakeyaSharp.tube δ (v i) (x i))) :=
    ⟨by simpa using volume_tube_lt_top δ (v i) (x i)⟩
  have hi : IntegrableOn f (KakeyaSharp.tube δ (v i) (x i)) volume :=
    (hf.mono_measure Measure.restrict_le_self).integrable (ENNReal.one_le_ofReal.mpr hp)
  have heq : tubeMass δ f (v i) (x i) =
      ENNReal.ofReal (∫ y in KakeyaSharp.tube δ (v i) (x i), ‖f y‖) :=
    (ofReal_integral_norm_eq_lintegral_enorm hi).symm
  rw [heq, ENNReal.ofReal_div_of_pos hk]
  exact ENNReal.div_le_div_left (hvol i (x i)) _

end KakeyaSharp

