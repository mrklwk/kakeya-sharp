/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.EnergySlices

@[expose] public section

/-! Fubini for the actual energy density on the Euclidean ball. -/

noncomputable section
open MeasureTheory Set Metric
namespace KakeyaSharp

theorem thinBall_section {m : ℕ} (x : Space m) (p : ThinTransverseSpace m) :
    (x, p) ∈ thinBall m ↔ p ∈ ball 0 (Real.sqrt (1 - ‖x‖ ^ 2)) := by
  change ‖x‖ ^ 2 + ‖p‖ ^ 2 < 1 ↔ dist p 0 < Real.sqrt (1 - ‖x‖ ^ 2)
  rw [dist_zero_right, Real.lt_sqrt (norm_nonneg p)]
  constructor <;> intro h <;> linarith

theorem thinEnergy_indicator_section {m : ℕ} (η : ℝ) (x : Space m) :
    (∫ p : ThinTransverseSpace m, (thinBall m).indicator (thinEnergyDensity η) (x, p)) =
      thinSliceEnergy η x := by
  unfold thinSliceEnergy
  rw [← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  by_cases h : (x, p) ∈ thinBall m
  · have hp := (thinBall_section x p).mp h
    simp [h, hp]
  · have hp : p ∉ ball 0 (Real.sqrt (1 - ‖x‖ ^ 2)) :=
      fun hp => h ((thinBall_section x p).mpr hp)
    simp [h, hp]

theorem thinSliceEnergy_zero_outside {m : ℕ} (η : ℝ) {x : Space m}
    (hx : x ∉ ball (0 : Space m) 1) : thinSliceEnergy η x = 0 := by
  have hx' : 1 ≤ ‖x‖ := by simpa [mem_ball, dist_zero_right] using hx
  have hs : 1 - ‖x‖ ^ 2 ≤ 0 := by nlinarith
  simp [thinSliceEnergy, Real.sqrt_eq_zero_of_nonpos hs]

theorem thinSliceEnergy_integrable {m : ℕ} {η : ℝ} (hη : 0 < η) :
    Integrable (thinSliceEnergy η : Space m → ℝ) := by
  have hi := (thinEnergyDensity_integrableOn hη).integrable_indicator (thinBall_measurable m)
  change Integrable _ ((volume : Measure (Space m)).prod volume) at hi
  exact hi.integral_prod_left.congr
    (Filter.Eventually.of_forall (thinEnergy_indicator_section η))

theorem thinEnergy_eq_slices {m : ℕ} {η : ℝ} (hη : 0 < η) :
    thinEnergy m η = ∫ x in ball (0 : Space m) 1, thinSliceEnergy η x := by
  have hi := (thinEnergyDensity_integrableOn hη).integrable_indicator (thinBall_measurable m)
  unfold thinEnergy
  rw [← integral_indicator (thinBall_measurable m)]
  change (∫ z, (thinBall m).indicator (thinEnergyDensity η) z
    ∂((volume : Measure (Space m)).prod volume)) = _
  rw [integral_prod _ hi]
  simp_rw [thinEnergy_indicator_section]
  rw [← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ ball (0 : Space m) 1
  · simp [hx]
  · simp [hx, thinSliceEnergy_zero_outside η hx]

end KakeyaSharp
