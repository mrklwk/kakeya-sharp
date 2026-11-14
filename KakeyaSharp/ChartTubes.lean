/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.DirectionCharts
public import KakeyaSharp.GraphWindow
public import KakeyaSharp.Packet.BroadGraphTubes

@[expose] public section

/-! The sharp weighted estimate for actual Euclidean tubes in one fixed
direction chart and a bounded interval of longitudinal centers. Transverse
centers are arbitrary; all logarithms and geometric scale losses are checked. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open Set Metric MeasureTheory Packet

def weightedTubeOverlap {n N : ℕ} (δ : ℝ) (v c : Fin N → Space n)
    (weights : Fin N → ℝ) (y : Space n) : ℝ :=
  ∑ l, (tube (2*δ) (v l) (c l)).indicator (fun _ => weights l) y

theorem weightedTubeOverlap_nonneg {n N : ℕ} (δ : ℝ) (v c : Fin N → Space n)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (y : Space n) :
    0 ≤ weightedTubeOverlap δ v c weights y :=
  Finset.sum_nonneg (fun l _ => Set.indicator_nonneg (fun _ _ => hw l) y)

theorem weightedTubeOverlap_measurable {n N : ℕ} (δ : ℝ) (v c : Fin N → Space n)
    (weights : Fin N → ℝ) : Measurable (weightedTubeOverlap δ v c weights) := by
  apply Finset.measurable_sum
  intro l _
  exact measurable_const.indicator (measurableSet_tube _ _ _)

theorem weightedTubeOverlap_power_le_window {m N : ℕ} (hm : 1 ≤ m)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (v c : Fin N → Space (m+1))
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (hv : ∀ l, ‖v l‖=1) (hnear : ∀ l, dist (v l) (north m) ≤ 1/16)
    (hc : ∀ l, c l 0 ∈ Icc (-2 : ℝ) 2) (y : Space (m+1)) :
    (weightedTubeOverlap δ v c weights y)^(inputExponent m) ≤
      powerWindow (256*δ) (fun l k => intercept (c l) (v l) k)
        (fun l k => slope (v l) k) weights (-5) 5 (coordinates m y) := by
  change _ ≤ if y 0 ∈ Icc (-5 : ℝ) 5 then
    (sliceOverlap (256*δ) (fun l k => intercept (c l) (v l) k)
      (fun l k => slope (v l) k) weights (y 0) (tail y))^(inputExponent m) else 0
  split_ifs with ht
  · apply Real.rpow_le_rpow (weightedTubeOverlap_nonneg δ v c hw y) _
      (le_trans (by norm_num) (inputExponent_ge_one hm))
    apply Finset.sum_le_sum
    intro l _
    by_cases hy : y ∈ tube (2*δ) (v l) (c l)
    · have hd : dist (tail y) (Packet.graphAxis
          (fun k => intercept (c l) (v l) k) (fun k => slope (v l) k) (y 0)) ≤ (256*δ)/64 := by
        have h := (tube_near_north_in_graph hδ1 (hv l) (hnear l) (hc l) hy).2
        linarith
      simp only [Set.indicator_of_mem hy,hd,ite_true,le_refl]
    · rw [Set.indicator_of_notMem hy]
      split_ifs <;> first | exact hw l | rfl
  · have he : weightedTubeOverlap δ v c weights y=0 := by
      apply Finset.sum_eq_zero
      intro l _
      exact Set.indicator_of_notMem (fun hy => ht
        (tube_near_north_in_graph hδ1 (hv l) (hnear l) (hc l) hy).1) _
    rw [he,Real.zero_rpow (by have hq := inputExponent_ge_one hm; linarith)]

theorem half_scale_log_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (2/(δ/2)) ≤ 2*Real.log (2/δ) := by
  have he : 2/(δ/2)=2*(2/δ) := by ring
  rw [he,Real.log_mul (by norm_num) (by positivity)]
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    ((le_div_iff₀ hδ).mpr (by linarith) : 2 ≤ 2/δ)
  linarith

theorem exists_chart_graph_window_constant {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v c : Fin N → Space (m+1)) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, ‖v l‖=1) →
      (∀ l, dist (v l) (north m) ≤ 1/16) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      (∫ y, powerWindow (256*δ) (fun l k => intercept (c l) (v l) k)
        (fun l k => slope (v l) k) weights (-5) 5 y) ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  obtain ⟨C,hC,hbound⟩ := exists_globalGraphTube_broad_timeInterval_constant hm
  refine ⟨20*C,mul_pos (by norm_num) hC,?_⟩
  intro N δ hδ hδ1 v c weights hw hv hnear hsep
  have h := hbound N 10 (δ/2) (-5) (by positivity) (by linarith)
    (fun l k => intercept (c l) (v l) k) (fun l k => slope (v l) k) weights hw
    (fun l => slope_sq_sum_of_near_north (hnear l)) (slope_separated v hv hnear hsep)
  have hscale : 512*(δ/2)=256*δ := by ring
  norm_num only [Nat.cast_ofNat,show (-5 : ℝ)+10=5 by norm_num,hscale] at h
  rw [powerWindow_integral (by omega : 1 ≤ m) (by positivity : 0 < 256*δ)
    (by norm_num) _ _ hw]
  have hS : 0 ≤ ∑ l, (weights l)^(inputExponent m) :=
    Finset.sum_nonneg (fun l _ => Real.rpow_nonneg (hw l) _)
  have hL : 0 ≤ Real.log (2/δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hp : (δ/2)^m ≤ δ^m := pow_le_pow_left₀ (by positivity) (by linarith) m
  calc
    _ ≤ 10*C*Real.log (2/(δ/2))*(δ/2)^m*(∑ l, (weights l)^(inputExponent m)) := h
    _ ≤ 10*C*(2*Real.log (2/δ))*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
      gcongr
      exact half_scale_log_le hδ hδ1
    _ = _ := by ring

/-- Actual radius-2-delta Euclidean tubes with arbitrary transverse centers,
longitudinal centers in [-2,2], and directions in the fixed small cap. -/
theorem exists_chartTube_constant {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v c : Fin N → Space (m+1)) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, ‖v l‖=1) →
      (∀ l, dist (v l) (north m) ≤ 1/16) →
      (∀ l, c l 0 ∈ Icc (-2 : ℝ) 2) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      (∫ y, (weightedTubeOverlap δ v c weights y)^(inputExponent m)) ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  obtain ⟨C,hC,hbound⟩ := exists_chart_graph_window_constant hm
  refine ⟨C,hC,?_⟩
  intro N δ hδ hδ1 v c weights hw hv hnear hc hsep
  let G := powerWindow (256*δ) (fun l k => intercept (c l) (v l) k)
    (fun l k => slope (v l) k) weights (-5) 5
  have hGi : Integrable G := powerWindow_integrable (by omega : 1 ≤ m)
    (by positivity : 0 < 256*δ) (by norm_num) _ _ hw
  have hGc : Integrable (fun y => G (coordinates m y)) :=
    (coordinates_measurePreserving m).integrable_comp_of_integrable hGi
  have hpoint := weightedTubeOverlap_power_le_window (by omega : 1 ≤ m) hδ hδ1 v c hw hv hnear hc
  have hmeas : Measurable (fun y => (weightedTubeOverlap δ v c weights y)^(inputExponent m)) :=
    (Real.continuous_rpow_const (le_trans (by norm_num) (inputExponent_ge_one (by omega : 1 ≤ m)))).measurable.comp
      (weightedTubeOverlap_measurable δ v c weights)
  have hi : Integrable (fun y => (weightedTubeOverlap δ v c weights y)^(inputExponent m)) := by
    apply hGc.mono' hmeas.aestronglyMeasurable
    apply ae_of_all
    intro y
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (weightedTubeOverlap_nonneg δ v c hw y) _)]
    exact hpoint y
  have h := integral_mono hi hGc hpoint
  rw [integral_coordinates] at h
  exact h.trans (hbound N δ hδ hδ1 v c weights hw hv hnear hsep)

end KakeyaSharp.Graph
