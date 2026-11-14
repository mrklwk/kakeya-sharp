/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinProfile
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

@[expose] public section

/-! Euclidean volume integrals in radial coordinates. -/

noncomputable section
open MeasureTheory Set Metric
namespace KakeyaSharp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem integral_ball_radial (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in ball (0 : E) R, f ‖x‖ ∂μ) =
      (Module.finrank ℝ E : ℝ) * μ.real (ball 0 1) *
        ∫ r in (0 : ℝ)..R, r ^ (Module.finrank ℝ E - 1) * f r := by
  have he : (ball (0 : E) R).indicator (fun x => f ‖x‖) =
      fun x => (Iio R).indicator f ‖x‖ := by
    funext x
    simp only [Set.indicator, mem_ball, dist_zero_right, mem_Iio]
  rw [← integral_indicator measurableSet_ball, he, integral_fun_norm_addHaar μ]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_assoc]
  congr 1
  have hi : (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) *
      (Iio R).indicator f r) =
      ∫ r in Ioi (0 : ℝ), (Ioo 0 R).indicator
        (fun r => r ^ (Module.finrank ℝ E - 1) * f r) r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change 0 < r at hr
    by_cases h : r < R <;> simp [Set.indicator, hr, h]
  rw [hi, integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo (0 : ℝ) R ⊆ Ioi 0 from fun _ h => h.1),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR]

/-- The Jacobian for replacing radius by its square, with no regularity hypothesis on f. -/
theorem integral_radius_square (k : ℕ) (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in (0 : ℝ)..R, r ^ (2 * k + 1) * f (r ^ 2)) =
      (1 / 2) * ∫ t in (0 : ℝ)..R ^ 2, t ^ k * f t := by
  have hh := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := R)
    (f := fun r : ℝ => r ^ 2) (f' := fun r : ℝ => 2 * r)
    (g := fun t => t ^ k * f t) (by fun_prop)
    (fun r _ => by simpa [Pi.pow_def] using (hasDerivAt_id r).pow 2)
    (fun r hr => by
      rw [min_eq_left hR, max_eq_right hR] at hr
      exact mul_nonneg (by norm_num) hr.1.le)
  simp only [Function.comp_def, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hh
  have he : (fun r : ℝ => (r ^ 2) ^ k * f (r ^ 2) * (2 * r)) =
      fun r => 2 * (r ^ (2 * k + 1) * f (r ^ 2)) := by
    funext r
    rw [pow_succ r (2 * k), pow_mul]
    ring
  rw [he, intervalIntegral.integral_const_mul] at hh
  linarith

/-- In even dimension 2m, the squared radial variable has density m V t^(m-1). -/
theorem integral_ball_norm_sq_even (m : ℕ) (hm : 1 ≤ m)
    (hdim : Module.finrank ℝ E = 2 * m) (f : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ x in ball (0 : E) (Real.sqrt s), f (‖x‖ ^ 2) ∂μ) =
      (m : ℝ) * μ.real (ball 0 1) * ∫ t in (0 : ℝ)..s, t ^ (m - 1) * f t := by
  rw [integral_ball_radial μ (fun r => f (r ^ 2)) (Real.sqrt_nonneg s), hdim]
  have hn : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  rw [hn, integral_radius_square (m - 1) f (Real.sqrt_nonneg s), Real.sq_sqrt hs]
  push_cast
  ring

/-- The boundary variable is `s = 1 - r²`. -/
theorem integral_boundary_variable (f : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..1, r * f (1 - r ^ 2)) = (1 / 2) * ∫ s in (0 : ℝ)..1, f s := by
  have hh := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (a := 0) (b := 1)
    (f := fun r : ℝ => 1 - r ^ 2) (f' := fun r : ℝ => -2 * r) (g := f)
    (by fun_prop)
    (fun r _ => by simpa [Pi.sub_def, Pi.pow_def] using
      (hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).pow 2))
    (fun r hr => by
      have hr0 : 0 ≤ r := by simpa using hr.1.le
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hr0)
  simp only [Function.comp_def, zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow,
    sub_zero, sub_self] at hh
  have hrev : (∫ u in (1 : ℝ)..0, f u) = -(∫ u in (0 : ℝ)..1, f u) :=
    intervalIntegral.integral_symm _ _
  rw [hrev] at hh
  have he : (fun r : ℝ => f (1 - r ^ 2) * (-2 * r)) =
      fun r => -2 * (r * f (1 - r ^ 2)) := by funext r; ring
  rw [he, intervalIntegral.integral_const_mul] at hh
  linarith

/-- For dimension at least two, boundary integration is bounded by a flat scalar integral. -/
theorem integral_ball_boundary_le (hdim : 2 ≤ Module.finrank ℝ E) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) (hf0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ f s) :
    (∫ x in ball (0 : E) 1, f (1 - ‖x‖ ^ 2) ∂μ) ≤
      ((Module.finrank ℝ E : ℝ) * μ.real (ball 0 1) / 2) * ∫ s in (0 : ℝ)..1, f s := by
  have hm (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : 1 - r ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hr.1, hr.2, sq_nonneg r]
  have hfc : ContinuousOn (fun r : ℝ => f (1 - r ^ 2)) (Icc 0 1) :=
    hf.comp (by fun_prop) hm
  have hp (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : r ^ (Module.finrank ℝ E - 1) ≤ r := by
    have he : Module.finrank ℝ E - 1 = (Module.finrank ℝ E - 2) + 1 := by omega
    rw [he, pow_succ]
    exact mul_le_of_le_one_left hr.1 (pow_le_one₀ hr.1 hr.2)
  rw [integral_ball_radial μ (fun r => f (1 - r ^ 2)) (by norm_num)]
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (((continuousOn_id.pow _).mul hfc).intervalIntegrable_of_Icc (by norm_num))
    ((continuousOn_id.mul hfc).intervalIntegrable_of_Icc (by norm_num))
    (fun r hr => mul_le_mul_of_nonneg_right (hp r hr) (hf0 _ (hm r hr)))
  simp only [Pi.mul_def, Pi.pow_def, id_eq] at h
  apply (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq
  rw [integral_boundary_variable]
  ring

end KakeyaSharp
