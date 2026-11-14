/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.EnergyBoundary

@[expose] public section

/-! A radial boundary estimate valid also in one spatial dimension.
Keeping radius rather than radius squared avoids a singular radial weight. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Metric
namespace KakeyaSharp

theorem boundaryKernel_radial_le {a r : ℝ} (ha : 0 < a) (hr : r ∈ Icc (0 : ℝ) 1) :
    boundaryKernel a (1-r^2) ≤ 1+1/(a+(1-r)) := by
  have hs : 0 ≤ 1-r^2 := by nlinarith [hr.1,hr.2]
  apply (boundaryKernel_le ha hs).trans
  apply add_le_add le_rfl
  apply one_div_le_one_div_of_le (by linarith [hr.2] : 0 < a+(1-r))
  nlinarith [hr.1,hr.2]

theorem spatial_boundary_integral_log_of_one_le {m : ℕ} (hm : 1 ≤ m) {η : ℝ}
    (hη : 0 < η) (hη10 : η ≤ 1/10) :
    (∫ x in ball (0 : Space m) 1, boundaryKernel (η^2) (1-‖x‖^2)) ≤
      6*(m : ℝ)*spatialVolume m*Real.log (1/η) := by
  let : NeZero m := ⟨by omega⟩
  have ha : 0 < η^2 := sq_pos_of_pos hη
  have hdim : Module.finrank ℝ (Space m)=m := by simp [Space]
  have hmaps (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : 1-r^2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hr.1,hr.2,sq_nonneg r]
  have hb : ContinuousOn (fun r : ℝ => boundaryKernel (η^2) (1-r^2)) (Icc 0 1) :=
    (boundaryKernel_continuousOn ha).comp (by fun_prop) hmaps
  have hf : ContinuousOn (fun r : ℝ => 1+1/(η^2+(1-r))) (Icc 0 1) := by
    apply continuousOn_const.add
    apply continuousOn_const.div (by fun_prop)
    intro r hr
    linarith [hr.2]
  have hpoint (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      r^(m-1)*boundaryKernel (η^2) (1-r^2) ≤ 1+1/(η^2+(1-r)) := by
    apply le_trans _ (boundaryKernel_radial_le ha hr)
    exact mul_le_of_le_one_left (boundaryKernel_nonneg ha (hmaps r hr))
      (pow_le_one₀ hr.1 hr.2)
  rw [integral_ball_radial volume (fun r => boundaryKernel (η^2) (1-r^2)) (by norm_num),hdim]
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (((continuousOn_id.pow _).mul hb).intervalIntegrable_of_Icc (by norm_num))
    (hf.intervalIntegrable_of_Icc (by norm_num)) hpoint
  have hchange : (∫ r in (0 : ℝ)..1, 1+1/(η^2+(1-r)))=
      1+Real.log ((η^2+1)/η^2) := by
    have hc := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun r : ℝ => 1+1/(η^2+r)) (1 : ℝ)
    norm_num only [sub_zero,sub_self] at hc
    rw [hc,intervalIntegral.integral_add intervalIntegrable_const]
    · rw [reciprocal_kernel_integral ha]
      norm_num
    · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      apply continuousOn_const.div (by fun_prop)
      intro r hr
      linarith [hr.1]
  rw [hchange] at h
  have hscalar : 1+Real.log ((η^2+1)/η^2) ≤ 6*Real.log (1/η) := by
    have ha1 : η^2 ≤ 1 := by nlinarith
    have hlower := Real.one_sub_inv_le_log_of_pos (show 0 < 1/η by positivity)
    simp only [one_div,inv_inv,Real.log_inv] at hlower
    have hupper := Real.log_le_sub_one_of_pos (show 0 < η^2+1 by positivity)
    rw [Real.log_div (by positivity : η^2+1 ≠ 0) ha.ne',Real.log_pow]
    simp only [one_div,Real.log_inv,Nat.cast_ofNat]
    nlinarith
  have hall := mul_le_mul_of_nonneg_left (h.trans hscalar)
    (show 0 ≤ (m : ℝ)*(volume : Measure (Space m)).real (ball 0 1) by positivity)
  convert hall using 1
  · rfl
  · unfold spatialVolume
    ring

end KakeyaSharp
