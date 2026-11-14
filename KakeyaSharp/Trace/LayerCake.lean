/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import Mathlib

@[expose] public section

/-! Integrating a scaled tail comparison. All measure-theoretic steps are
independent of the Monge–Ampère operator. -/
noncomputable section
namespace KakeyaSharp
open MeasureTheory Set Filter
open scoped ENNReal

theorem lintegral_moment_le_of_scaled_tails {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (m : ℕ) {H : ℝ} (_hH : 0 ≤ H) {U : X → ℝ}
    (hUμ : 0 ≤ᵐ[μ] U) (hUν : 0 ≤ᵐ[ν] U) (hU : Measurable U)
    (htail : ∀ t : ℝ, 0 < t → ENNReal.ofReal (t^m)*ν {x | 3*t < U x} ≤
      ENNReal.ofReal (H^m)*μ {x | t < U x}) :
    (∫⁻ x, ENNReal.ofReal (U x ^ (m+1)) ∂ν) ≤
      ENNReal.ofReal ((3 : ℝ)^(m+1)*((m : ℝ)+1)*H^m) * ∫⁻ x, ENNReal.ofReal (U x) ∂μ := by
  have hdiv : 0 ≤ᵐ[ν] (fun x => U x/3) := hUν.mono (fun x hx => div_nonneg hx (by norm_num))
  have hmoment := lintegral_rpow_eq_lintegral_meas_lt_mul ν hdiv
    (hU.div_const 3).aemeasurable (show (0 : ℝ) < (m+1 : ℕ) by positivity)
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast] at hmoment
  have hp (x : ℝ) : x^((m : ℝ)+1) = x^(m+1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.rpow_natCast x (m+1)
  simp_rw [hp] at hmoment
  have hsets (t : ℝ) : {x | t < U x/3} = {x | 3*t < U x} := by
    ext x
    simp only [mem_ofPred_eq, lt_div_iff₀ (show (0 : ℝ) < 3 by norm_num)]
    rw [mul_comm t 3]
  have hcompare : (∫⁻ t in Ioi (0 : ℝ), ν {x | t < U x/3}*ENNReal.ofReal (t^m)) ≤
      ENNReal.ofReal (H^m) * ∫⁻ x, ENNReal.ofReal (U x) ∂μ := by
    rw [lintegral_eq_lintegral_meas_lt μ hUμ hU.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hsets, mul_comm]
    exact htail t ht
  have hscale : (∫⁻ x, ENNReal.ofReal (U x ^ (m+1)) ∂ν) =
      ENNReal.ofReal ((3 : ℝ)^(m+1)) * ∫⁻ x, ENNReal.ofReal ((U x/3)^(m+1)) ∂ν := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow]
    field_simp
  rw [hscale, hmoment]
  calc
    _ ≤ ENNReal.ofReal ((3 : ℝ)^(m+1)) *
        (ENNReal.ofReal ((m : ℝ)+1)*(ENNReal.ofReal (H^m)*∫⁻ x, ENNReal.ofReal (U x) ∂μ)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hcompare)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]

theorem withDensity_ofReal_apply_eq_integral_indicator {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {d : X → ℝ} (hd : Integrable d μ) (hd0 : 0 ≤ᵐ[μ] d)
    {s : Set X} (hs : MeasurableSet s) :
    (μ.withDensity (fun x => ENNReal.ofReal (d x))) s =
      ENNReal.ofReal (∫ x, s.indicator d x ∂μ) := by
  classical
  rw [withDensity_apply _ hs, ofReal_integral_eq_lintegral_ofReal (hd.indicator hs)]
  · rw [← lintegral_indicator hs]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  · filter_upwards [hd0] with x hx
    change 0 ≤ d x at hx
    by_cases hxs : x ∈ s <;> simp [hxs, hx]

theorem lintegral_withDensity_ofReal_eq_integral {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {d f : X → ℝ} (hd : Measurable d) (hf : Measurable f)
    (hd0 : 0 ≤ᵐ[μ] d) (hf0 : 0 ≤ᵐ[μ] f) (hi : Integrable (fun x => f x*d x) μ) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ.withDensity (fun x => ENNReal.ofReal (d x))) =
      ENNReal.ofReal (∫ x, f x*d x ∂μ) := by
  rw [lintegral_withDensity_eq_lintegral_mul μ hd.ennreal_ofReal hf.ennreal_ofReal,
    ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards [hd0, hf0] with x hx hy; exact mul_nonneg hy hx)]
  apply lintegral_congr_ae
  filter_upwards [hd0] with x hx
  change ENNReal.ofReal (d x)*ENNReal.ofReal (f x) = ENNReal.ofReal (f x*d x)
  rw [mul_comm (f x), ENNReal.ofReal_mul hx]

end KakeyaSharp
