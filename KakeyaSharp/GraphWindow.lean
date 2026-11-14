/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.GraphCoordinates

@[expose] public section

/-! Product integrability and exact Fubini for the graph overlap on a
finite time interval. These identities connect the graph estimate to
Lebesgue integration in the actual Euclidean ambient space. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open Set Metric MeasureTheory Packet

def powerWindow {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (s t : ℝ) (y : ℝ × Space m) : ℝ :=
  if y.1 ∈ Icc s t then (sliceOverlap δ a v weights y.1 y.2)^(inputExponent m) else 0

theorem powerWindow_nonneg {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (s t : ℝ) (y : ℝ × Space m) :
    0 ≤ powerWindow δ a v weights s t y := by
  unfold powerWindow
  split_ifs <;> first
    | exact Real.rpow_nonneg (sliceOverlap_nonneg δ a v hw y.1 y.2) _
    | rfl

theorem powerWindow_measurable {m N : ℕ} (hm : 1 ≤ m) (δ : ℝ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) (s t : ℝ) :
    Measurable (powerWindow δ a v weights s t) := by
  apply Measurable.ite (measurableSet_Icc.preimage measurable_fst) _ measurable_const
  exact (Real.continuous_rpow_const (le_trans (by norm_num) (inputExponent_ge_one hm))).measurable.comp
    (sliceOverlap_measurable δ a v weights)

theorem powerWindow_slice_integral {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (s t u : ℝ) :
    (∫ x, powerWindow δ a v weights s t (u,x))=
      (Icc s t).indicator (sliceIntegral δ a v weights) u := by
  by_cases h : u ∈ Icc s t <;> simp [powerWindow,h,sliceIntegral]

theorem powerWindow_integrable {m N : ℕ} (hm : 1 ≤ m) {δ s t : ℝ}
    (hδ : 0 < δ) (hst : s ≤ t) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) :
    Integrable (powerWindow δ a v weights s t) := by
  apply (integrable_prod_iff (powerWindow_measurable hm δ a v weights s t).aestronglyMeasurable).mpr
  constructor
  · apply ae_of_all
    intro u
    by_cases h : u ∈ Icc s t
    · simpa only [powerWindow,h,ite_true] using
        sliceOverlap_power_integrable δ (inputExponent_ge_one hm) a v hw u
    · simpa only [powerWindow,h,ite_false] using
        (show Integrable (fun _ : Space m => (0 : ℝ)) from integrable_zero (Space m) ℝ volume)
  · have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mp
      (sliceIntegral_intervalIntegrable_all hm hδ a v hw s t)
    have he (u : ℝ) :
        (∫ x, ‖powerWindow δ a v weights s t (u,x)‖)=
          (Icc s t).indicator (sliceIntegral δ a v weights) u := by
      simp_rw [Real.norm_of_nonneg (powerWindow_nonneg δ a v hw s t _)]
      exact powerWindow_slice_integral δ a v weights s t u
    simp_rw [he]
    exact hi.integrable_indicator measurableSet_Icc

theorem powerWindow_integral {m N : ℕ} (hm : 1 ≤ m) {δ s t : ℝ}
    (hδ : 0 < δ) (hst : s ≤ t) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) :
    (∫ y, powerWindow δ a v weights s t y)=∫ u in s..t, sliceIntegral δ a v weights u := by
  change (∫ y, powerWindow δ a v weights s t y ∂volume.prod volume)=_
  rw [integral_prod _ (powerWindow_integrable hm hδ hst a v hw)]
  simp_rw [powerWindow_slice_integral]
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hst]

end KakeyaSharp.Graph
