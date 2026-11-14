/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.RadialIntegrals

@[expose] public section

/-! The one-dimensional boundary integral in the logarithmic energy estimate.
`RadialVolume` and `ThinEnergy` connect it to the full Euclidean volume integral. -/

noncomputable section
open MeasureTheory Set
namespace KakeyaSharp

def boundaryKernel (a s : ℝ) : ℝ :=
  s / (a + s) + s * (1 - s) / (a + s) ^ 2

theorem boundaryKernel_le {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    boundaryKernel a s ≤ 1 + 1 / (a + s) := by
  have hd : 0 < a + s := by linarith
  have h1 : s / (a + s) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have h2 : s * (1 - s) / (a + s) ^ 2 ≤ 1 / (a + s) := by
    calc
      _ ≤ (a + s) / (a + s) ^ 2 :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg s]) (sq_nonneg _)
      _ = _ := by field_simp
  exact add_le_add h1 h2

theorem reciprocal_kernel_integral {a : ℝ} (ha : 0 < a) :
    (∫ s in (0 : ℝ)..1, 1 / (a + s)) = Real.log ((a + 1) / a) := by
  have hi : IntervalIntegrable (fun s : ℝ => 1 / (a + s)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro s hs
    linarith [hs.1]
  have hh : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.log (a + t)) (1 / (a + s)) s := by
    intro s hs
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hd : a + s ≠ 0 := by linarith [hs.1]
    simpa only [Pi.add_def, zero_add, id_eq] using
      (((hasDerivAt_const s a).add (hasDerivAt_id s)).log hd)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hh hi]
  simp only [add_zero, Real.log_div (by linarith : a + 1 ≠ 0) ha.ne']

theorem boundary_kernel_integral_le {a : ℝ} (ha : 0 < a) :
    (∫ s in (0 : ℝ)..1, boundaryKernel a s) ≤ 1 + Real.log ((a + 1) / a) := by
  have hden : ∀ s ∈ Icc (0 : ℝ) 1, a + s ≠ 0 := by
    intro s hs
    linarith [hs.1]
  have hi : IntervalIntegrable (boundaryKernel a) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (ContinuousOn.div (by fun_prop) (by fun_prop) hden).add
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun s hs => pow_ne_zero _ (hden s hs)))
  have hj : IntervalIntegrable (fun s : ℝ => 1 / (a + s)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact ContinuousOn.div continuousOn_const (by fun_prop) hden
  calc
    _ ≤ ∫ s in (0 : ℝ)..1, (1 + 1 / (a + s)) :=
      intervalIntegral.integral_mono_on (by norm_num) hi (intervalIntegrable_const.add hj)
        (fun s hs => boundaryKernel_le ha hs.1)
    _ = _ := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hj, reciprocal_kernel_integral ha]
      simp

/-- After setting `a = η²`, the last radial integral costs only one logarithm. -/
theorem boundary_kernel_integral_log {η : ℝ} (hη : 0 < η) (hη10 : η ≤ 1 / 10) :
    (∫ s in (0 : ℝ)..1, boundaryKernel (η ^ 2) s) ≤ 6 * Real.log (1 / η) := by
  have ha : 0 < η ^ 2 := sq_pos_of_pos hη
  have ha1 : η ^ 2 ≤ 1 := by nlinarith
  have hlower := Real.one_sub_inv_le_log_of_pos (show 0 < 1 / η by positivity)
  simp only [one_div, inv_inv, Real.log_inv] at hlower
  have hupper := Real.log_le_sub_one_of_pos (show 0 < η ^ 2 + 1 by positivity)
  apply (boundary_kernel_integral_le ha).trans
  rw [Real.log_div (by positivity : η ^ 2 + 1 ≠ 0) ha.ne', Real.log_pow]
  simp only [one_div, Real.log_inv, Nat.cast_ofNat]
  nlinarith

end KakeyaSharp
