/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.EnergyBoundaryAllDimensions

@[expose] public section

/-! The logarithmic bound for the actual determinant energy of the thin test. -/

noncomputable section
open MeasureTheory Set Metric
namespace KakeyaSharp

def thinEnergyConstant (m : ℕ) : ℝ :=
  1 + (4 * 6 ^ (m - 1)) * ((m : ℝ) * transverseVolume m) *
    spatialVolume m * (6 + 6 * (m : ℝ))

theorem thinEnergyConstant_pos (m : ℕ) : 0 < thinEnergyConstant m := by
  unfold thinEnergyConstant transverseVolume spatialVolume
  positivity

theorem thinEnergy_le_log {m : ℕ} (hm : 1 ≤ m) {η : ℝ}
    (hη : 0 < η) (hη10 : η ≤ 1 / 10) :
    thinEnergy m η ≤ thinEnergyConstant m * Real.log (1 / η) := by
  have ha : 0 < η ^ 2 := sq_pos_of_pos hη
  have hm1 : 1 ≤ m := by omega
  have hm1' : 1 ≤ (m : ℝ) := by exact_mod_cast hm1
  let c : ℝ := (4 * 6 ^ (m - 1)) * ((m : ℝ) * transverseVolume m)
  have hc : 0 ≤ c := by dsimp [c, transverseVolume]; positivity
  have hl : 0 ≤ Real.log (1 / η) :=
    Real.log_nonneg ((le_div_iff₀ hη).mpr (by linarith))
  have hbint := boundary_composition_integrableOn (m := m) (boundaryKernel_continuousOn ha)
  have hconst : IntegrableOn (fun _x : Space m => 6 * Real.log (1 / η)) (ball 0 1) :=
    integrableOn_const
  have hslicebound (x : Space m) (hx : x ∈ ball 0 1) :
      thinSliceEnergy η x ≤ c * (6 * Real.log (1 / η) +
        boundaryKernel (η ^ 2) (1 - ‖x‖ ^ 2)) := by
    have hxc := ball_subset_closedBall hx
    have hs := boundary_variable_mem hxc
    have hx' : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hxc
    have hln : 0 ≤ Real.log ((η ^ 2 + (1 - ‖x‖ ^ 2)) / η ^ 2) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ ha).mpr
      linarith [hs.1]
    have hld := (div_le_self hln hm1').trans (log_ratio_le_log hη hη10 hs)
    exact (thinSliceEnergy_le hm1 hη hx').trans
      (mul_le_mul_of_nonneg_left (add_le_add hld le_rfl) hc)
  rw [thinEnergy_eq_slices hη]
  calc
    _ ≤ ∫ x in ball (0 : Space m) 1,
        c * (6 * Real.log (1 / η) + boundaryKernel (η ^ 2) (1 - ‖x‖ ^ 2)) := by
      exact setIntegral_mono_on (thinSliceEnergy_integrable hη).integrableOn
        ((hconst.add hbint).const_mul c) measurableSet_ball hslicebound
    _ = c * (spatialVolume m * (6 * Real.log (1 / η)) +
        ∫ x in ball (0 : Space m) 1, boundaryKernel (η ^ 2) (1 - ‖x‖ ^ 2)) := by
      rw [integral_const_mul, integral_add hconst hbint]
      simp [spatialVolume]
    _ ≤ c * (spatialVolume m * (6 * Real.log (1 / η)) +
        6 * (m : ℝ) * spatialVolume m * Real.log (1 / η)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (spatial_boundary_integral_log_of_one_le hm hη hη10)) hc
    _ ≤ thinEnergyConstant m * Real.log (1 / η) := by
      dsimp [c, thinEnergyConstant]
      nlinarith

theorem thinEnergy_log_bound {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 10 →
      thinEnergy m η ≤ C * Real.log (1 / η) :=
  ⟨thinEnergyConstant m, thinEnergyConstant_pos m,
    fun _ hη hη10 => thinEnergy_le_log hm hη hη10⟩

end KakeyaSharp
