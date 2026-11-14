/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Definitions

@[expose] public section

/-! Quantitative radial integrals used in the logarithmic output test.
Here `a` corresponds to the regularizing parameter η². -/

open MeasureTheory Set

noncomputable section
namespace KakeyaSharp

lemma radial_primitive_derivative (k : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    HasDerivAt (fun u : ℝ ↦ (u / (a + u)) ^ (k + 1) / (k + 1 : ℝ))
      (t ^ k * a / (a + t) ^ (k + 2)) t := by
  have hd : a + t ≠ 0 := (add_pos_of_pos_of_nonneg ha ht).ne'
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  have h := (((hasDerivAt_id t).div
    ((hasDerivAt_const t a).add (hasDerivAt_id t)) hd).pow (k + 1)).div_const (k + 1 : ℝ)
  convert h using 1
  · rfl
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, one_mul, mul_one,
      Pi.add_apply, Pi.div_apply, id_eq, zero_add]
    rw [div_pow, pow_add]
    field_simp
    ring

lemma radial_kernel_integrable (k : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ k * a / (a + t) ^ (k + 2)) volume 0 s := by
  apply ContinuousOn.intervalIntegrable_of_Icc hs
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro t ht
  exact pow_ne_zero _ (add_pos_of_pos_of_nonneg ha ht.1).ne'

theorem radial_kernel_integral (k : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, t ^ k * a / (a + t) ^ (k + 2)) =
      (s / (a + s)) ^ (k + 1) / (k + 1 : ℝ) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) s,
      HasDerivAt (fun u : ℝ ↦ (u / (a + u)) ^ (k + 1) / (k + 1 : ℝ))
        (t ^ k * a / (a + t) ^ (k + 2)) t := by
    intro t ht
    rw [uIcc_of_le hs] at ht
    exact radial_primitive_derivative k ha ht.1
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (radial_kernel_integrable k ha hs)

theorem radial_kernel_integral_le (k : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, t ^ k * a / (a + t) ^ (k + 2)) ≤ 1 / (k + 1 : ℝ) := by
  rw [radial_kernel_integral k ha hs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_one₀ (div_nonneg hs (by linarith))
  exact (div_le_one (by linarith)).mpr (by linarith)

lemma log_primitive_derivative {a s t : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    HasDerivAt (fun u : ℝ ↦ (a + u) * (1 + Real.log (a + s) - Real.log (a + u)))
      (Real.log ((a + s) / (a + t))) t := by
  have hd : a + t ≠ 0 := (add_pos_of_pos_of_nonneg ha ht).ne'
  have has : a + s ≠ 0 := (add_pos_of_pos_of_nonneg ha hs).ne'
  have hsum := (hasDerivAt_const t a).add (hasDerivAt_id t)
  have h := hsum.mul ((hasDerivAt_const t (1 + Real.log (a + s))).sub (hsum.log hd))
  convert h using 1
  · rfl
  · simp only [Pi.add_apply, Pi.sub_apply, id_eq, zero_add, one_mul]
    rw [Real.log_div has hd]
    field_simp
    ring

lemma log_kernel_integrable {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    IntervalIntegrable (fun t : ℝ ↦ Real.log ((a + s) / (a + t))) volume 0 s := by
  apply ContinuousOn.intervalIntegrable_of_Icc hs
  apply ContinuousOn.log
  · apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact (add_pos_of_pos_of_nonneg ha ht.1).ne'
  · intro t ht
    exact (div_pos (by linarith) (by linarith [ht.1])).ne'

theorem log_kernel_integral {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, Real.log ((a + s) / (a + t))) =
      s - a * Real.log ((a + s) / a) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) s,
      HasDerivAt (fun u : ℝ ↦ (a + u) * (1 + Real.log (a + s) - Real.log (a + u)))
        (Real.log ((a + s) / (a + t))) t := by
    intro t ht
    rw [uIcc_of_le hs] at ht
    exact log_primitive_derivative ha hs ht.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (log_kernel_integrable ha hs)]
  rw [Real.log_div (by linarith : a + s ≠ 0) ha.ne']
  simp only [add_zero]
  ring

theorem log_kernel_integral_le {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, Real.log ((a + s) / (a + t))) ≤ s := by
  rw [log_kernel_integral ha hs]
  have hlog : 0 ≤ Real.log ((a + s) / a) := by
    apply Real.log_nonneg
    exact (one_le_div ha).mpr (by linarith)
  nlinarith

/-- This is the second radial estimate in the manuscript, with no unspecified constant. -/
theorem weighted_log_kernel_integral_le (k : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, (t / (a + t)) ^ k * Real.log ((a + s) / (a + t))) ≤ s := by
  have hw : IntervalIntegrable (fun t : ℝ ↦ (t / (a + t)) ^ k) volume 0 s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hs
    apply ContinuousOn.pow
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact (add_pos_of_pos_of_nonneg ha ht.1).ne'
  have hcont : ContinuousOn (fun t : ℝ ↦ (t / (a + t)) ^ k *
      Real.log ((a + s) / (a + t))) (Icc 0 s) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.pow
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht
      exact (add_pos_of_pos_of_nonneg ha ht.1).ne'
    · apply ContinuousOn.log
      · apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro t ht
        exact (add_pos_of_pos_of_nonneg ha ht.1).ne'
      · intro t ht
        exact (div_pos (by linarith) (by linarith [ht.1])).ne'
  apply le_trans (intervalIntegral.integral_mono_on hs
    (hcont.intervalIntegrable_of_Icc hs) (log_kernel_integrable ha hs) ?_)
    (log_kernel_integral_le ha hs)
  intro t ht
  have hd : 0 < a + t := by linarith [ht.1]
  have hpow : (t / (a + t)) ^ k ≤ 1 :=
    pow_le_one₀ (div_nonneg ht.1 hd.le) ((div_le_one hd).mpr (by linarith))
  have hlog : 0 ≤ Real.log ((a + s) / (a + t)) := by
    apply Real.log_nonneg
    exact (one_le_div hd).mpr (by linarith [ht.2])
  exact mul_le_of_le_one_left hlog hpow

end KakeyaSharp
