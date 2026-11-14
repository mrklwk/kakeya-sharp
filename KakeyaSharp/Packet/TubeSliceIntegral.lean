/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.TubeSlices
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Measurability and integrability of the spatial overlap integral as
a function of time. A uniform bound follows from the individual tube volumes. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

def sliceIntegral {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (sliceOverlap δ a v weights t x)^(inputExponent m)

theorem sliceIntegral_nonneg {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (t : ℝ) :
    0 ≤ sliceIntegral δ a v weights t :=
  integral_nonneg (fun x => Real.rpow_nonneg (sliceOverlap_nonneg δ a v hw t x) _)

theorem sliceIntegral_measurable {m N : ℕ} (hm : 1 ≤ m) (δ : ℝ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    Measurable (sliceIntegral δ a v weights) := by
  have h := (Real.continuous_rpow_const
    (le_trans (by norm_num) (inputExponent_ge_one hm))).measurable.comp
      (sliceOverlap_measurable δ a v weights)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem sliceMajorant_integral {m N : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (q : ℝ) (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) (t : ℝ) :
    (∫ x, sliceMajorant δ q a v weights t x) =
      (δ/64)^m*directionMass m*(∑ l, (weights l)^q) := by
  unfold sliceMajorant
  rw [integral_finsetSum]
  · simp only [integral_indicator measurableSet_closedBall,integral_const,
      measureReal_restrict_apply_univ,smul_eq_mul,
      direction_closedBall_volume hm _ (by positivity : 0 ≤ δ/64)]
    exact (Finset.mul_sum _ _ _).symm
  · intro l _
    exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall

theorem sliceIntegral_uniform_bound {m N : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) :
    ∃ C : ℝ, ∀ t, |sliceIntegral δ a v weights t| ≤ C := by
  refine ⟨(N : ℝ)^(inputExponent m-1)*
    ((δ/64)^m*directionMass m*(∑ l, (weights l)^(inputExponent m))),?_⟩
  intro t
  rw [abs_of_nonneg (sliceIntegral_nonneg δ a v hw t)]
  have h := integral_mono
    (sliceOverlap_power_integrable δ (inputExponent_ge_one hm) a v hw t)
    ((sliceMajorant_integrable δ (inputExponent m) a v weights t).const_mul _)
    (sliceOverlap_power_le δ (inputExponent_ge_one hm) a v hw t)
  rwa [integral_const_mul,sliceMajorant_integral hm hδ] at h

theorem sliceIntegral_intervalIntegrable {m N : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) :
    IntervalIntegrable (sliceIntegral δ a v weights) volume 0 1 := by
  obtain ⟨C,hC⟩ := sliceIntegral_uniform_bound hm hδ a v hw
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply (integrableOn_const (μ := volume) (s := Icc (0 : ℝ) 1)
    isCompact_Icc.measure_ne_top (C := C)).mono'
    (sliceIntegral_measurable hm δ a v weights).aestronglyMeasurable
  exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using hC t)

end KakeyaSharp.Packet
