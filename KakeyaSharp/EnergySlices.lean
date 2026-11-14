/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.EnergyIntegrability
public import KakeyaSharp.EnergyKernels
public import KakeyaSharp.RadialVolume

@[expose] public section

/-! Integration of the determinant energy in the 2m transverse coordinates. -/

noncomputable section
open MeasureTheory Set Metric
namespace KakeyaSharp
open KakeyaSharp.Moore

def energyMajorant (k : ℕ) (a s t : ℝ) : ℝ :=
  Real.log ((a + s) / (a + t)) *
    (a / (a + t) ^ (k + 2) +
      (1 / (a + s) + (1 - s) / (a + s) ^ 2) / (a + t) ^ k)

theorem energyMajorant_radial (k : ℕ) (a s t : ℝ) :
    t ^ k * energyMajorant k a s t = radialEnergyKernel k a s t := by
  unfold energyMajorant radialEnergyKernel
  rw [div_pow]
  ring

theorem energyMajorant_norm_continuous {E : Type*} [NormedAddCommGroup E]
    (k : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    Continuous (fun p : E => energyMajorant k a s (‖p‖ ^ 2)) := by
  unfold energyMajorant
  have hd : Continuous (fun p : E => a + ‖p‖ ^ 2) := by fun_prop
  have hn (p : E) : a + ‖p‖ ^ 2 ≠ 0 := by positivity
  have hl := (continuous_const.div hd hn).log
    (fun p : E => (div_pos (show 0 < a + s by positivity)
      (show 0 < a + ‖p‖ ^ 2 by positivity)).ne')
  exact hl.mul ((continuous_const.div (hd.pow _) (fun p => pow_ne_zero _ (hn p))).add
    (continuous_const.div (hd.pow _) (fun p => pow_ne_zero _ (hn p))))

theorem thinEnergyDensity_le_majorant {m : ℕ} (hm : 1 ≤ m) {η : ℝ} (hη : 0 < η)
    {z : ThinSpace m} (hz : z ∈ thinClosedBall m) :
    thinEnergyDensity η z ≤ (4 * 6 ^ (m - 1)) *
      energyMajorant (m - 1) (η ^ 2) (1 - ‖z.1‖ ^ 2) (‖z.2‖ ^ 2) := by
  have hb := thinNumerator_pos hη z
  have hd := thinDenominator_pos hη hz
  have h := mul_le_mul_of_nonneg_left (thinProfile_determinant_bound hm hη hz)
    (neg_nonneg.mpr (thinProfile_nonpos hη hz))
  change thinEnergyDensity η z ≤ _ at h
  convert h using 1
  unfold energyMajorant thinProfile
  have he : m - 1 + 2 = m + 1 := by omega
  rw [he, Real.log_div hb.ne' hd.ne']
  have hden : η ^ 2 + (1 - ‖z.1‖ ^ 2) = thinDenominator η z := by
    unfold thinDenominator
    ring
  rw [hden]
  change _ = _
  rw [show η ^ 2 + ‖z.2‖ ^ 2 = thinNumerator η z from rfl,
    Real.log_div hd.ne' hb.ne']
  ring

def transverseVolume (m : ℕ) : ℝ :=
  (volume : Measure (ThinTransverseSpace m)).real (ball 0 1)

def thinSliceEnergy {m : ℕ} (η : ℝ) (x : Space m) : ℝ :=
  ∫ p in ball (0 : ThinTransverseSpace m) (Real.sqrt (1 - ‖x‖ ^ 2)),
    thinEnergyDensity η (x, p)

theorem thinSliceEnergy_le {m : ℕ} (hm : 1 ≤ m) {η : ℝ} (hη : 0 < η)
    {x : Space m} (hx : ‖x‖ ≤ 1) :
    thinSliceEnergy η x ≤ (4 * 6 ^ (m - 1)) * ((m : ℝ) * transverseVolume m) *
      (Real.log ((η ^ 2 + (1 - ‖x‖ ^ 2)) / η ^ 2) / m +
        boundaryKernel (η ^ 2) (1 - ‖x‖ ^ 2)) := by
  let : NeZero m := ⟨by omega⟩
  have ha : 0 < η ^ 2 := sq_pos_of_pos hη
  let s := 1 - ‖x‖ ^ 2
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    dsimp [s]
    constructor <;> nlinarith [norm_nonneg x, sq_nonneg ‖x‖]
  have hmem (p : ThinTransverseSpace m) (hp : p ∈ closedBall 0 (Real.sqrt s)) :
      (x, p) ∈ thinClosedBall m := by
    have hp' : ‖p‖ ≤ Real.sqrt s := by simpa [mem_closedBall, dist_zero_right] using hp
    change ‖x‖ ^ 2 + ‖p‖ ^ 2 ≤ 1
    have ht := Real.sq_sqrt hs.1
    dsimp [s] at ht
    nlinarith [norm_nonneg p, Real.sqrt_nonneg s]
  have hi : IntegrableOn (fun p : ThinTransverseSpace m => thinEnergyDensity η (x, p))
      (ball 0 (Real.sqrt s)) := by
    have hc := (thinEnergyDensity_continuousOn hη).comp
      (continuous_const.prodMk continuous_id).continuousOn hmem
    exact (hc.integrableOn_compact (isCompact_closedBall 0 (Real.sqrt s))).mono_set ball_subset_closedBall
  have hj := ((energyMajorant_norm_continuous (E := ThinTransverseSpace m)
    (m - 1) ha hs.1).continuousOn.integrableOn_compact (μ := volume)
    (isCompact_closedBall 0 (Real.sqrt s))).mono_set ball_subset_closedBall
  have hdim : Module.finrank ℝ (ThinTransverseSpace m) = 2 * m := by
    simp [ThinTransverseSpace, mul_comm]
  have hrad := integral_ball_norm_sq_even (volume : Measure (ThinTransverseSpace m))
    m hm hdim (energyMajorant (m - 1) (η ^ 2) s) hs.1
  simp_rw [energyMajorant_radial] at hrad
  have hcoef : 0 ≤ (4 * 6 ^ (m - 1) : ℝ) * ((m : ℝ) * transverseVolume m) := by
    unfold transverseVolume
    positivity
  calc
    _ ≤ ∫ p in ball (0 : ThinTransverseSpace m) (Real.sqrt s),
        (4 * 6 ^ (m - 1)) * energyMajorant (m - 1) (η ^ 2) s (‖p‖ ^ 2) := by
      apply setIntegral_mono_on hi (hj.const_mul _) measurableSet_ball
      intro p hp
      exact thinEnergyDensity_le_majorant hm hη (hmem p (ball_subset_closedBall hp))
    _ = (4 * 6 ^ (m - 1)) * ((m : ℝ) * transverseVolume m) *
        ∫ t in (0 : ℝ)..s, radialEnergyKernel (m - 1) (η ^ 2) s t := by
      rw [integral_const_mul, hrad]
      unfold transverseVolume
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (radial_energy_slice_le (m - 1) ha hs) hcoef
      have hn : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        exact_mod_cast (show m - 1 + 1 = m by omega)
      simpa only [hn, s] using hh

end KakeyaSharp
