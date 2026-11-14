/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Trace.Comparison

@[expose] public section

/-! A sublevel mass bound for the trace inequality. The dimensional constant
will come from a fixed factor three in the level, not from mixed determinants. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Matrix.Norms.Elementwise

theorem thinQuaternionHessian_sub_const {m : ℕ} (f : ThinSpace m → ℝ) (c : ℝ) (z : ThinSpace m) :
    thinQuaternionHessian (fun x => f x-c) z = thinQuaternionHessian f z := by
  have he : fderiv ℝ (fun x => f x-c) = fderiv ℝ f := by
    funext x
    exact fderiv_sub_const c
  unfold thinQuaternionHessian thinRealHessian
  rw [he]

theorem thinDet_nonneg {m : ℕ} {f : ThinSpace m → ℝ} {z : ThinSpace m}
    (hf : ContDiffAt ℝ 2 f z)
    (hpos : ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian f z) a) :
    0 ≤ mooreDet m (thinQuaternionHessian f z) :=
  mooreDet_nonneg_of_complexify_posSemidef _
    ((complexify_posSemidef_iff (thinQuaternionHessian_isHermitian hf)).mpr hpos)

theorem thinDet_sublevel_bound {m : ℕ} {R H t : ℝ}
    (hR : 0 < R) (hH : 0 < H) (ht : 0 < t) (o : ThinSpace m)
    {u φ : ThinSpace m → ℝ} (hu : ContDiff ℝ 3 u) (hφ : ContDiff ℝ 3 φ)
    (hzu : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2=R^2 → u z=0)
    (hbound : ∀ z ∈ thinClosedBallAt R o, -H ≤ φ z ∧ φ z ≤ 0)
    (hpu : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian u z) a)
    (hpφ : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian φ z) a) :
    (t/H)^m * (∫ z in thinBallAt R o,
      if 3*t < -u z then mooreDet m (thinQuaternionHessian φ z) else 0) ≤
      ∫ z in thinBallAt R o, if t < -u z then mooreDet m (thinQuaternionHessian u z) else 0 := by
  classical
  let w : ThinSpace m → ℝ := fun z => (t/H)*φ z-t
  let χ : ℝ → ℝ := fun s => Real.smoothTransition (s/t)
  have hw : ContDiff ℝ 3 w := (contDiff_const.mul hφ).sub contDiff_const
  have hχ : ContDiff ℝ 1 χ := Real.smoothTransition.contDiff.comp (contDiff_id.div_const t)
  have hχmono : Monotone χ := fun x y hxy => Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right hxy ht.le)
  have hχnonneg (s : ℝ) : 0 ≤ χ s := Real.smoothTransition.nonneg _
  have hχle (s : ℝ) : χ s ≤ 1 := Real.smoothTransition.le_one _
  have hclosed (z : ThinSpace m) (hz : z ∈ thinBallAt R o) : z ∈ thinClosedBallAt R o :=
    show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le
  have hHw (z : ThinSpace m) : thinQuaternionHessian w z = (t/H)•thinQuaternionHessian φ z := by
    rw [show w = fun x => ((t/H)•φ) x-t by rfl, thinQuaternionHessian_sub_const,
      thinQuaternionHessian_smul]
  have hDw (z : ThinSpace m) : mooreDet m (thinQuaternionHessian w z) =
      (t/H)^m*mooreDet m (thinQuaternionHessian φ z) := by rw [hHw, mooreDet_smul]
  have hzero : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2=R^2 → χ (w z-u z)=0 := by
    intro z hz
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ ht.le
    have hb := (hbound z hz.le).2
    have hm := mul_nonpos_of_nonneg_of_nonpos (div_pos ht hH).le hb
    dsimp [w]
    rw [hzu z hz]
    linarith
  have hcmp := thinDet_smooth_comparison hR o hu hw hχ hχmono hzero hpu
    (fun z hz a => by rw [hHw, quaternionForm_smul]; exact mul_nonneg (div_pos ht hH).le (hpφ z hz a))
  have hc : Continuous (fun z => χ (w z-u z)) := hχ.continuous.comp (hw.continuous.sub hu.continuous)
  have hdetφ : Continuous (fun z => mooreDet m (thinQuaternionHessian φ z)) :=
    (KakeyaSharp.continuous_mooreDet m).comp (thinHessian_continuous hφ)
  have hdetu : Continuous (fun z => mooreDet m (thinQuaternionHessian u z)) :=
    (KakeyaSharp.continuous_mooreDet m).comp (thinHessian_continuous hu)
  have hlarge : MeasurableSet {z : ThinSpace m | 3*t < -u z} :=
    isOpen_lt continuous_const hu.continuous.neg |>.measurableSet
  have hsmall : MeasurableSet {z : ThinSpace m | t < -u z} :=
    isOpen_lt continuous_const hu.continuous.neg |>.measurableSet
  have hiφ := (continuous_integrableOn_thinBallAt hR o hdetφ).indicator hlarge
  have hiu := (continuous_integrableOn_thinBallAt hR o hdetu).indicator hsmall
  have hleft : (t/H)^m * (∫ z in thinBallAt R o,
      if 3*t < -u z then mooreDet m (thinQuaternionHessian φ z) else 0) ≤
      ∫ z in thinBallAt R o, χ (w z-u z)*mooreDet m (thinQuaternionHessian w z) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hiφ.const_mul _)
      (continuous_integrableOn_thinBallAt hR o (hc.mul
        ((KakeyaSharp.continuous_mooreDet m).comp (thinHessian_continuous hw)))) (thinBallAt_measurable R o)
    intro z hz
    change (t/H)^m*(if 3*t < -u z then mooreDet m (thinQuaternionHessian φ z) else 0) ≤
      χ (w z-u z)*mooreDet m (thinQuaternionHessian w z)
    rw [hDw]
    have hφpos := thinDet_nonneg (hφ.contDiffAt.of_le (by norm_num)) (hpφ z hz)
    split_ifs with hlarge'
    · have hb := (hbound z (hclosed z hz)).1
      have hb' : -t ≤ (t/H)*φ z := by
        have hh := mul_le_mul_of_nonneg_left hb (div_pos ht hH).le
        field_simp at hh ⊢
        nlinarith
      have hc1 : χ (w z-u z)=1 := by
        apply Real.smoothTransition.one_of_one_le
        apply (le_div_iff₀ ht).mpr
        dsimp [w]
        nlinarith
      rw [hc1, one_mul]
    · simp only [mul_zero]
      exact mul_nonneg (hχnonneg _) (mul_nonneg (pow_nonneg (div_pos ht hH).le m) hφpos)
  have hright : (∫ z in thinBallAt R o, χ (w z-u z)*mooreDet m (thinQuaternionHessian u z)) ≤
      ∫ z in thinBallAt R o, if t < -u z then mooreDet m (thinQuaternionHessian u z) else 0 := by
    apply setIntegral_mono_on (continuous_integrableOn_thinBallAt hR o (hc.mul hdetu)) hiu
      (thinBallAt_measurable R o)
    intro z hz
    change χ (w z-u z)*mooreDet m (thinQuaternionHessian u z) ≤
      (if t < -u z then mooreDet m (thinQuaternionHessian u z) else 0)
    have hup := thinDet_nonneg (hu.contDiffAt.of_le (by norm_num)) (hpu z hz)
    split_ifs with hsmall'
    · exact mul_le_of_le_one_left hup (hχle _)
    · have hb := (hbound z (hclosed z hz)).2
      have hm := mul_nonpos_of_nonneg_of_nonpos (div_pos ht hH).le hb
      have hc0 : χ (w z-u z)=0 := by
        apply Real.smoothTransition.zero_of_nonpos
        apply div_nonpos_of_nonpos_of_nonneg _ ht.le
        dsimp [w]
        linarith
      rw [hc0, zero_mul]
  exact hleft.trans (hcmp.trans hright)

end KakeyaSharp
