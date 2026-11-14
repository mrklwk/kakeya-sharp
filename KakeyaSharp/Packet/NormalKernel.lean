/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.RadialVolume
public import KakeyaSharp.RadialIntegrals

@[expose] public section

/-! A uniform whole-space integral bound for the 2m-dimensional normal
kernel. The proof reuses the exact radial primitive already checked. -/
noncomputable section
set_option maxHeartbeats 800000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory Filter
open scoped Topology

def normalKernel (m : ℕ) (h : ℝ) (P : ThinTransverseSpace m) : ℝ :=
  h/(h+‖P‖^2)^(m+1)

def normalMass (m : ℕ) : ℝ :=
  volume.real (ball (0 : ThinTransverseSpace m) 1)

theorem normalMass_nonneg (m : ℕ) : 0 ≤ normalMass m := ENNReal.toReal_nonneg

theorem normalMass_pos (m : ℕ) : 0 < normalMass m :=
  ENNReal.toReal_pos (measure_ball_pos volume (0 : ThinTransverseSpace m) (by norm_num)).ne'
    measure_ball_lt_top.ne

theorem normalKernel_nonneg (m : ℕ) {h : ℝ} (hh : 0 < h) (P : ThinTransverseSpace m) :
    0 ≤ normalKernel m h P := by unfold normalKernel; positivity

theorem normalKernel_continuous (m : ℕ) {h : ℝ} (hh : 0 < h) :
    Continuous (normalKernel m h) := by
  apply Continuous.div continuous_const (by fun_prop)
  intro P
  exact pow_ne_zero _ (show 0 < h+‖P‖^2 by positivity).ne'

theorem normalKernel_ball_integral_le {m : ℕ} (hm : 1 ≤ m) {h R : ℝ}
    (hh : 0 < h) (hR : 0 ≤ R) :
    (∫ P in ball (0 : ThinTransverseSpace m) R, normalKernel m h P) ≤ normalMass m := by
  let : NeZero m := ⟨by omega⟩
  have hdim : Module.finrank ℝ (ThinTransverseSpace m) = 2*m := by simp [ThinTransverseSpace,mul_comm]
  have hrad := integral_ball_norm_sq_even (volume : Measure (ThinTransverseSpace m))
    m hm hdim (fun t => h/(h+t)^(m+1)) (sq_nonneg R)
  rw [Real.sqrt_sq hR] at hrad
  have hexp : m+1=(m-1)+2 := by omega
  have hmcast : ((m-1 : ℕ) : ℝ)+1=m := by exact_mod_cast (show m-1+1=m by omega)
  have hscalar : (∫ t in (0 : ℝ)..R^2, t^(m-1)*(h/(h+t)^(m+1))) ≤ 1/(m : ℝ) := by
    simpa only [hexp, hmcast, mul_div_assoc] using radial_kernel_integral_le (m-1) hh (sq_nonneg R)
  change (∫ P in ball (0 : ThinTransverseSpace m) R, h/(h+‖P‖^2)^(m+1)) ≤ _
  rw [hrad]
  have hmult := mul_le_mul_of_nonneg_left hscalar
    (show 0 ≤ (m : ℝ)*volume.real (ball (0 : ThinTransverseSpace m) 1) by positivity)
  apply hmult.trans_eq
  unfold normalMass
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp

theorem normalKernel_integrable {m : ℕ} (hm : 1 ≤ m) {h : ℝ} (hh : 0 < h) :
    Integrable (normalKernel m h) := by
  have hc := aecover_ball (μ := (volume : Measure (ThinTransverseSpace m))) (x := 0)
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply hc.integrable_of_integral_bounded_of_nonneg_ae (normalMass m)
  · intro n
    exact ((normalKernel_continuous m hh).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ThinTransverseSpace m) (n : ℝ))).mono_set ball_subset_closedBall
  · exact ae_of_all _ (normalKernel_nonneg m hh)
  · exact Eventually.of_forall (fun n => normalKernel_ball_integral_le hm hh (Nat.cast_nonneg n))

theorem normalKernel_integral_le {m : ℕ} (hm : 1 ≤ m) {h : ℝ} (hh : 0 < h) :
    (∫ P, normalKernel m h P) ≤ normalMass m := by
  have hc := aecover_ball (μ := (volume : Measure (ThinTransverseSpace m))) (x := 0)
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  exact le_of_tendsto (hc.integral_tendsto_of_countably_generated (normalKernel_integrable hm hh))
    (Eventually.of_forall (fun n => normalKernel_ball_integral_le hm hh (Nat.cast_nonneg n)))

end KakeyaSharp.Packet
