/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinConcavity

@[expose] public section

/-! Smooth comparison of determinant masses, using only the first cofactor
and its Green identity. No mixed-determinant positivity is assumed. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Matrix.Norms.Elementwise

theorem hasDerivAt_weighted_thinDet {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {u v w : ThinSpace m → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hw : Continuous w) (t : ℝ) :
    HasDerivAt (fun s => ∫ z in thinBallAt R o, w z * mooreDet m
      (thinQuaternionHessian (u+s•v) z))
      (∫ z in thinBallAt R o, w z * mooreDifferential m
        (thinQuaternionHessian (u+t•v) z) (thinQuaternionHessian v z)) t := by
  simp only [thinQuaternionHessian_affine (hu.of_le (by norm_num)) (hv.of_le (by norm_num))]
  let F : ℝ × ThinSpace m → ℝ := fun p => w p.2 * mooreDet m
    (thinQuaternionHessian u p.2+p.1•thinQuaternionHessian v p.2)
  let F' : ℝ × ThinSpace m → ℝ := fun p => w p.2 * mooreDifferential m
    (thinQuaternionHessian u p.2+p.1•thinQuaternionHessian v p.2) (thinQuaternionHessian v p.2)
  have hA : Continuous (fun p : ℝ × ThinSpace m =>
      thinQuaternionHessian u p.2+p.1•thinQuaternionHessian v p.2) :=
    ((thinHessian_continuous hu).comp continuous_snd).add
      (continuous_fst.smul ((thinHessian_continuous hv).comp continuous_snd))
  exact hasDerivAt_setIntegral_compact (μ := volume) (thinBallAt_measurable R o)
    (thinClosedBallAt_compact hR.le o)
    (fun z hz => show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)
    ((hw.comp continuous_snd).mul ((KakeyaSharp.continuous_mooreDet m).comp hA))
    ((hw.comp continuous_snd).mul (continuous_thinDifferential_affine hu hv))
    (fun s z => (hasDerivAt_mooreDet_affine (thinQuaternionHessian u z)
      (thinQuaternionHessian v z) s).const_mul (w z)) t

theorem thinCofactor_composition_green {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {u v : ThinSpace m → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 2 v)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hz : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2=R^2 → χ (v z)=0) :
    (∫ z in thinBallAt R o, χ (v z)*mooreDifferential m
      (thinQuaternionHessian u z) (thinQuaternionHessian v z)) =
      -(∫ z in thinBallAt R o, deriv χ (v z)*
        quaternionForm (thinCofactor u z) (thinQuaternionGradient v z)) := by
  let : (volume : Measure (ThinSpace m)).IsAddHaarMeasure := by
    change ((volume : Measure (Space m)).prod (volume : Measure (ThinTransverseSpace m))).IsAddHaarMeasure
    infer_instance
  have hgrad (z : ThinSpace m) (d : ThinSpace m) :
      fderiv ℝ (fun x => χ (v x)) z d = deriv χ (v z)*fderiv ℝ v z d := by
    have h := ((hχ.differentiable (by norm_num) (v z)).hasDerivAt.comp_hasFDerivAt z
      (hv.differentiable (by norm_num) z).hasFDerivAt).fderiv
    exact congrArg (fun L => L d) h
  have hg := Green.moore_cofactor_green_bounded threeSlots
    (fun p => thinDirection p.1 p.2) (thinBallAt_isOpen R o)
    (thinBallAt_bounded hR.le o) (thinBallAt_null_frontier R o) hu
    (hχ.comp (hv.of_le (by norm_num))) hv
    (fun z hz' => hz z (thinBallAt_frontier_subset R o hz'))
  change (∫ z in thinBallAt R o, χ (v z)*mooreDifferential m
      (thinQuaternionHessian u z) (thinQuaternionHessian v z)) =
    -(∫ z in thinBallAt R o, ∑ p, ∑ q, realCoefficients threeSlots (thinCofactor u z) p q *
      fderiv ℝ (fun x => χ (v x)) z (thinDirection p.1 p.2) *
      fderiv ℝ v z (thinDirection q.1 q.2)) at hg
  rw [hg]
  congr 1
  apply setIntegral_congr_fun (thinBallAt_measurable R o)
  intro z _
  change (∑ p, ∑ q, realCoefficients threeSlots (thinCofactor u z) p q *
    fderiv ℝ (fun x => χ (v x)) z (thinDirection p.1 p.2) *
    fderiv ℝ v z (thinDirection q.1 q.2)) = _
  simp only [hgrad]
  have hquad : (∑ p, ∑ q, realCoefficients threeSlots (thinCofactor u z) p q *
      fderiv ℝ v z (thinDirection p.1 p.2)*fderiv ℝ v z (thinDirection q.1 q.2)) =
      quaternionForm (thinCofactor u z) (thinQuaternionGradient v z) := by
    simp_rw [mul_assoc]
    exact Green.realCoefficients_quadratic _ threeSlots _
  rw [← hquad, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem thinCofactor_composition_nonpos {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {u v : ThinSpace m → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 2 v)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχmono : Monotone χ)
    (hz : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2=R^2 → χ (v z)=0)
    (hpos : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian u z) a) :
    (∫ z in thinBallAt R o, χ (v z)*mooreDifferential m
      (thinQuaternionHessian u z) (thinQuaternionHessian v z)) ≤ 0 := by
  rw [thinCofactor_composition_green hR o hu hv hχ hz]
  apply neg_nonpos.mpr
  apply setIntegral_nonneg (thinBallAt_measurable R o)
  intro z hz'
  exact mul_nonneg (hχmono.deriv_nonneg) (mooreCofactor_quaternionForm_nonneg _
    (thinQuaternionHessian_isHermitian (hu.contDiffAt.of_le (by norm_num))) (hpos z hz') _)

theorem thinDet_smooth_comparison {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {u v : ThinSpace m → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχmono : Monotone χ)
    (hz : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2=R^2 → χ (v z-u z)=0)
    (hpu : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian u z) a)
    (hpv : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian v z) a) :
    (∫ z in thinBallAt R o, χ (v z-u z)*mooreDet m (thinQuaternionHessian v z)) ≤
      ∫ z in thinBallAt R o, χ (v z-u z)*mooreDet m (thinQuaternionHessian u z) := by
  let F : ℝ → ℝ := fun t => ∫ z in thinBallAt R o, χ (v z-u z)*
    mooreDet m (thinQuaternionHessian (u+t•(v-u)) z)
  let F' : ℝ → ℝ := fun t => ∫ z in thinBallAt R o, χ (v z-u z)*
    mooreDifferential m (thinQuaternionHessian (u+t•(v-u)) z) (thinQuaternionHessian (v-u) z)
  have hd (t : ℝ) : HasDerivAt F (F' t) t := hasDerivAt_weighted_thinDet hR o hu (hv.sub hu)
    (hχ.continuous.comp (hv.continuous.sub hu.continuous)) t
  have hsign (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) : F' t ≤ 0 := by
    exact thinCofactor_composition_nonpos hR o (u := u+t•(v-u)) (v := v-u)
      (hu.add (contDiff_const.smul (hv.sub hu))) ((hv.sub hu).of_le (by norm_num)) hχ hχmono hz
      (fun z hz' => thinHessian_segment_nonneg (hu.of_le (by norm_num)) (hv.of_le (by norm_num))
        (hpu z hz') (hpv z hz') (interior_subset ht))
  have ha : AntitoneOn F (Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (f' := F') (convex_Icc (0 : ℝ) 1)
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt) hsign
  have h := ha (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) zero_le_one
  have he : u+(v-u)=v := by abel
  simpa only [F, zero_smul, add_zero, one_smul, he] using h

end KakeyaSharp
