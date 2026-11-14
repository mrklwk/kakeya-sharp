/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.EnergyFubini

@[expose] public section

/-! The remaining spatial integral in the determinant energy. -/

noncomputable section
open MeasureTheory Set Metric
namespace KakeyaSharp

def spatialVolume (m : ℕ) : ℝ :=
  (volume : Measure (Space m)).real (ball 0 1)

theorem boundaryKernel_continuousOn {a : ℝ} (ha : 0 < a) :
    ContinuousOn (boundaryKernel a) (Icc 0 1) := by
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, a + s ≠ 0 := by
    intro s hs
    linarith [hs.1]
  exact (ContinuousOn.div (by fun_prop) (by fun_prop) hd).add
    (ContinuousOn.div (by fun_prop) (by fun_prop) (fun s hs => pow_ne_zero _ (hd s hs)))

theorem boundaryKernel_nonneg {a s : ℝ} (ha : 0 < a) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ boundaryKernel a s := by
  unfold boundaryKernel
  exact add_nonneg (div_nonneg hs.1 (by linarith [hs.1]))
    (div_nonneg (mul_nonneg hs.1 (sub_nonneg.mpr hs.2)) (sq_nonneg _))

theorem boundary_variable_mem {m : ℕ} {x : Space m} (hx : x ∈ closedBall 0 1) :
    1 - ‖x‖ ^ 2 ∈ Icc (0 : ℝ) 1 := by
  have hx' : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hx
  constructor <;> nlinarith [norm_nonneg x, sq_nonneg ‖x‖]

theorem boundary_composition_integrableOn {m : ℕ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) :
    IntegrableOn (fun x : Space m => f (1 - ‖x‖ ^ 2)) (ball 0 1) := by
  have hc := hf.comp (by fun_prop : ContinuousOn (fun x : Space m => 1 - ‖x‖ ^ 2)
    (closedBall 0 1)) (fun _ hx => boundary_variable_mem hx)
  exact (hc.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall

theorem spatial_boundary_integral_log {m : ℕ} (hm : 2 ≤ m) {η : ℝ}
    (hη : 0 < η) (hη10 : η ≤ 1 / 10) :
    (∫ x in ball (0 : Space m) 1, boundaryKernel (η ^ 2) (1 - ‖x‖ ^ 2)) ≤
      3 * (m : ℝ) * spatialVolume m * Real.log (1 / η) := by
  let : NeZero m := ⟨by omega⟩
  have ha : 0 < η ^ 2 := sq_pos_of_pos hη
  have hdim : Module.finrank ℝ (Space m) = m := by simp [Space]
  have hh := integral_ball_boundary_le (volume : Measure (Space m))
    (by simpa only [hdim] using hm) (boundaryKernel (η ^ 2))
    (boundaryKernel_continuousOn ha) (fun _ hs => boundaryKernel_nonneg ha hs)
  rw [hdim] at hh
  apply hh.trans
  have hh' := mul_le_mul_of_nonneg_left (boundary_kernel_integral_log hη hη10)
    (show 0 ≤ (m : ℝ) * (volume : Measure (Space m)).real (ball 0 1) / 2 by positivity)
  convert hh' using 1
  unfold spatialVolume
  ring

theorem log_ratio_le_log {η : ℝ} (hη : 0 < η) (hη10 : η ≤ 1 / 10)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Real.log ((η ^ 2 + s) / η ^ 2) ≤ 6 * Real.log (1 / η) := by
  have ha : 0 < η ^ 2 := sq_pos_of_pos hη
  have hmono : Real.log ((η ^ 2 + s) / η ^ 2) ≤ Real.log ((η ^ 2 + 1) / η ^ 2) := by
    apply Real.log_le_log (div_pos (by linarith [hs.1]) ha)
    exact div_le_div_of_nonneg_right (by linarith [hs.2]) ha.le
  apply hmono.trans
  have ha1 : η ^ 2 ≤ 1 := by nlinarith
  have hlower := Real.one_sub_inv_le_log_of_pos (show 0 < 1 / η by positivity)
  simp only [one_div, inv_inv, Real.log_inv] at hlower
  have hupper := Real.log_le_sub_one_of_pos (show 0 < η ^ 2 + 1 by positivity)
  rw [Real.log_div (by positivity : η ^ 2 + 1 ≠ 0) ha.ne', Real.log_pow]
  simp only [one_div, Real.log_inv, Nat.cast_ofNat]
  nlinarith

theorem spatial_log_integral {m : ℕ} {η : ℝ} (hη : 0 < η) (hη10 : η ≤ 1 / 10) :
    (∫ x in ball (0 : Space m) 1,
      Real.log ((η ^ 2 + (1 - ‖x‖ ^ 2)) / η ^ 2)) ≤
        6 * spatialVolume m * Real.log (1 / η) := by
  have ha : 0 < η ^ 2 := sq_pos_of_pos hη
  have hf : ContinuousOn (fun s : ℝ => Real.log ((η ^ 2 + s) / η ^ 2)) (Icc 0 1) := by
    apply ContinuousOn.log (by fun_prop)
    intro s hs
    exact (div_pos (by linarith [hs.1]) ha).ne'
  calc
    _ ≤ ∫ _x in ball (0 : Space m) 1, 6 * Real.log (1 / η) := by
      apply setIntegral_mono_on (boundary_composition_integrableOn hf)
        (integrableOn_const (measure_ball_lt_top.ne) ) measurableSet_ball
      intro x hx
      exact log_ratio_le_log hη hη10 (boundary_variable_mem (ball_subset_closedBall hx))
    _ = _ := by simp [spatialVolume, mul_comm, mul_left_comm, mul_assoc]

end KakeyaSharp
