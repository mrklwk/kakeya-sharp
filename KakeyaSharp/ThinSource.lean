/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.VariationalTest

@[expose] public section

/-! The source contribution of the logarithmic test on its thin central region. -/

noncomputable section
open MeasureTheory Set Metric
namespace KakeyaSharp

def thinCore (m : ℕ) (η : ℝ) : Set (ThinSpace m) :=
  ball (0 : Space m) (1 / 2) ×ˢ ball (0 : ThinTransverseSpace m) η

def thinCoreConstant (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ m * spatialVolume m * transverseVolume m

theorem thinCoreConstant_pos (m : ℕ) : 0 < thinCoreConstant m := by
  have hx : 0 < spatialVolume m :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : Space m) (by norm_num)).ne'
      measure_ball_lt_top.ne
  have hp : 0 < transverseVolume m :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : ThinTransverseSpace m) (by norm_num)).ne'
      measure_ball_lt_top.ne
  unfold thinCoreConstant
  positivity

theorem thinCore_measurable (m : ℕ) (η : ℝ) : MeasurableSet (thinCore m η) :=
  measurableSet_ball.prod measurableSet_ball

theorem thinCore_subset {m : ℕ} {η : ℝ} (hη : 0 < η) (hη10 : η ≤ 1 / 10) :
    thinCore m η ⊆ thinBall m := by
  intro z hz
  have hx : ‖z.1‖ < 1 / 2 := by simpa [mem_ball, dist_zero_right] using hz.1
  have hp : ‖z.2‖ < η := by simpa [mem_ball, dist_zero_right] using hz.2
  change ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < 1
  nlinarith [norm_nonneg z.1, norm_nonneg z.2]

theorem thinCore_volume {m : ℕ} {η : ℝ} (hη : 0 < η) :
    (volume : Measure (ThinSpace m)).real (thinCore m η) =
      thinCoreConstant m * η ^ (2 * m) := by
  change ((volume : Measure (Space m)).prod volume).real
    (ball 0 (1 / 2) ×ˢ ball (0 : ThinTransverseSpace m) η) = _
  rw [measureReal_prod_prod]
  have hx : (volume : Measure (Space m)).real (ball 0 (1 / 2)) =
      (1 / 2 : ℝ) ^ m * spatialVolume m := by
    unfold spatialVolume
    simp only [measureReal_def]
    rw [Measure.addHaar_ball_of_pos volume _ (by norm_num : (0 : ℝ) < 1 / 2)]
    simp [Space]
  have hp : (volume : Measure (ThinTransverseSpace m)).real (ball 0 η) =
      η ^ (2 * m) * transverseVolume m := by
    unfold transverseVolume
    simp only [measureReal_def]
    rw [Measure.addHaar_ball_of_pos volume _ hη, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hη.le _)]
    simp [ThinTransverseSpace, mul_comm]
  rw [hx, hp]
  unfold thinCoreConstant
  ring

theorem thinSource_integrableOn {m : ℕ} {η : ℝ} (hη : 0 < η)
    {μ : ThinSpace m → ℝ} (hμ : ContinuousOn μ (thinClosedBall m)) :
    IntegrableOn (fun z => (-thinProfile η z) * μ z) (thinBall m) := by
  have hc : ContinuousOn (thinProfile η : ThinSpace m → ℝ) (thinClosedBall m) :=
    fun _ hz => (thinProfile_smooth hη hz).continuousAt.continuousWithinAt
  exact ((hc.neg.mul hμ).integrableOn_compact (thinClosedBall_compact m)).mono_set
    (fun z hz => show ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1 from hz.le)

theorem thinSource_integral_lower {m : ℕ} {η a : ℝ}
    (hη : 0 < η) (hη10 : η ≤ 1 / 10)
    {μ : ThinSpace m → ℝ} (hμ : ContinuousOn μ (thinClosedBall m))
    (hμ0 : ∀ z ∈ thinBall m, 0 ≤ μ z)
    (hμa : ∀ z ∈ thinCore m η, a ≤ μ z) :
    thinCoreConstant m * η ^ (2 * m) * a * Real.log (1 / η) ≤
      ∫ z in thinBall m, (-thinProfile η z) * μ z := by
  have hi := thinSource_integrableOn hη hμ
  have hsub := thinCore_subset (m := m) hη hη10
  have hl : 0 ≤ Real.log (1 / η) :=
    Real.log_nonneg ((le_div_iff₀ hη).mpr (by linarith))
  calc
    _ = ∫ _z in thinCore m η, a * Real.log (1 / η) := by
      rw [setIntegral_const, thinCore_volume hη]
      simp only [smul_eq_mul]
      ring
    _ ≤ ∫ z in thinCore m η, (-thinProfile η z) * μ z := by
      have hc : IntegrableOn (fun _z : ThinSpace m => a * Real.log (1 / η))
          (thinCore m η) := by
        exact integrableOn_const ((measure_mono (show thinCore m η ⊆ thinClosedBall m from
          fun z hz => show ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1 from (hsub hz).le)).trans_lt
            (thinClosedBall_compact m).measure_lt_top |>.ne)
      apply setIntegral_mono_on hc (hi.mono_set hsub) (thinCore_measurable m η)
      intro z hz
      have hx : ‖z.1‖ ≤ 1 / 2 := by
        exact (show ‖z.1‖ < 1 / 2 by simpa [mem_ball, dist_zero_right] using hz.1).le
      have hp : ‖z.2‖ ≤ η := by
        exact (show ‖z.2‖ < η by simpa [mem_ball, dist_zero_right] using hz.2).le
      have hh := mul_le_mul (hμa z hz) (thinProfile_core_depth hη hη10 hx hp)
        hl (hμ0 z (hsub hz))
      simpa only [mul_comm] using hh
    _ ≤ _ := by
      apply setIntegral_mono_set hi
      · exact (ae_restrict_mem (thinBall_measurable m)).mono
          (fun z hz => mul_nonneg (neg_nonneg.mpr (thinProfile_nonpos hη hz.le)) (hμ0 z hz))
      · exact Filter.Eventually.of_forall (fun _ hz => hsub hz)

end KakeyaSharp
