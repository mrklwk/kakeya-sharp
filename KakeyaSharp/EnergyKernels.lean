/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.BoundaryIntegrals

@[expose] public section

/-! Integral estimates for the pointwise determinant majorant. -/

noncomputable section
open MeasureTheory Set
namespace KakeyaSharp

theorem radial_log_kernel_integral_le (k : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s,
      (t ^ k * a / (a + t) ^ (k + 2)) * Real.log ((a + s) / (a + t))) ≤
      Real.log ((a + s) / a) / (k + 1 : ℝ) := by
  have hrc : ContinuousOn (fun t : ℝ => t ^ k * a / (a + t) ^ (k + 2)) (Icc 0 s) :=
    ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun t ht => pow_ne_zero _ (add_pos_of_pos_of_nonneg ha ht.1).ne')
  have hlc : ContinuousOn (fun t : ℝ => Real.log ((a + s) / (a + t))) (Icc 0 s) := by
    apply ContinuousOn.log
    · exact ContinuousOn.div continuousOn_const (by fun_prop)
        (fun t ht => (add_pos_of_pos_of_nonneg ha ht.1).ne')
    · intro t ht
      exact (div_pos (by linarith) (by linarith [ht.1])).ne'
  have hL : 0 ≤ Real.log ((a + s) / a) :=
    Real.log_nonneg ((one_le_div ha).mpr (by linarith))
  calc
    _ ≤ ∫ t in (0 : ℝ)..s,
        Real.log ((a + s) / a) * (t ^ k * a / (a + t) ^ (k + 2)) := by
      apply intervalIntegral.integral_mono_on hs
        ((hrc.mul hlc).intervalIntegrable_of_Icc hs)
        ((radial_kernel_integrable k ha hs).const_mul _) 
      intro t ht
      have hd : 0 < a + t := by linarith [ht.1]
      have hlog : Real.log ((a + s) / (a + t)) ≤ Real.log ((a + s) / a) :=
        Real.log_le_log (div_pos (by linarith) hd)
          (div_le_div_of_nonneg_left (by linarith) ha (by linarith [ht.1]))
      have hk : 0 ≤ t ^ k * a / (a + t) ^ (k + 2) :=
        div_nonneg (mul_nonneg (pow_nonneg ht.1 _) ha.le) (pow_nonneg hd.le _)
      simpa only [Pi.mul_apply, mul_comm] using mul_le_mul_of_nonneg_left hlog hk
    _ = Real.log ((a + s) / a) *
        ∫ t in (0 : ℝ)..s, t ^ k * a / (a + t) ^ (k + 2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (radial_kernel_integral_le k ha hs) hL

def radialEnergyKernel (k : ℕ) (a s t : ℝ) : ℝ :=
  (t ^ k * a / (a + t) ^ (k + 2)) * Real.log ((a + s) / (a + t)) +
  (1 / (a + s) + (1 - s) / (a + s) ^ 2) *
    ((t / (a + t)) ^ k * Real.log ((a + s) / (a + t)))

theorem radialEnergyKernel_continuous (k : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    ContinuousOn (radialEnergyKernel k a s) (Icc 0 s) := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 s) : a + t ≠ 0 := by linarith [ht.1]
  have hl : ContinuousOn (fun t : ℝ => Real.log ((a + s) / (a + t))) (Icc 0 s) := by
    apply ContinuousOn.log
    · exact ContinuousOn.div continuousOn_const (by fun_prop) hd
    · intro t ht
      exact (div_pos (by linarith) (by linarith [ht.1])).ne'
  exact ((ContinuousOn.div (by fun_prop) (by fun_prop)
    (fun t ht => pow_ne_zero _ (hd t ht))).mul hl).add
    (continuousOn_const.mul
      (((ContinuousOn.div (by fun_prop) (by fun_prop) hd).pow k).mul hl))

theorem radial_energy_slice_le (k : ℕ) {a s : ℝ} (ha : 0 < a) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..s, radialEnergyKernel k a s t) ≤
      Real.log ((a + s) / a) / (k + 1 : ℝ) + boundaryKernel a s := by
  have hd : 0 < a + s := by linarith [hs.1]
  have hcoef : 0 ≤ 1 / (a + s) + (1 - s) / (a + s) ^ 2 := by
    apply add_nonneg (by positivity)
    exact div_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg _)
  have hr : ContinuousOn (fun t : ℝ => t ^ k * a / (a + t) ^ (k + 2)) (Icc 0 s) :=
    ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun t ht => pow_ne_zero _ (add_pos_of_pos_of_nonneg ha ht.1).ne')
  have hl : ContinuousOn (fun t : ℝ => Real.log ((a + s) / (a + t))) (Icc 0 s) := by
    apply ContinuousOn.log
    · exact ContinuousOn.div continuousOn_const (by fun_prop)
        (fun t ht => (add_pos_of_pos_of_nonneg ha ht.1).ne')
    · intro t ht
      exact (div_pos hd (by linarith [ht.1])).ne'
  have hw : ContinuousOn (fun t : ℝ => (t / (a + t)) ^ k) (Icc 0 s) :=
    (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun t ht => (add_pos_of_pos_of_nonneg ha ht.1).ne')).pow k
  have hri := (hr.mul hl).intervalIntegrable_of_Icc (μ := volume) hs.1
  have hwi := (hw.mul hl).intervalIntegrable_of_Icc (μ := volume) hs.1
  simp only [Pi.mul_def] at hri hwi
  unfold radialEnergyKernel
  rw [intervalIntegral.integral_add hri (hwi.const_mul _),
    intervalIntegral.integral_const_mul]
  have h := add_le_add (radial_log_kernel_integral_le k ha hs.1)
    (mul_le_mul_of_nonneg_left (weighted_log_kernel_integral_le k ha hs.1) hcoef)
  convert h using 1
  unfold boundaryKernel
  ring

end KakeyaSharp
