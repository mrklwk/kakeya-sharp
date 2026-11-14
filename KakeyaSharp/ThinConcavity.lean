/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinSecondVariation

@[expose] public section

/-! Concavity and the supporting inequality for the actual functional.
The positivity hypotheses are on the actual Hessians of the competitors. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Matrix.Norms.Elementwise

theorem thinFunctional_concave_line {m : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {ρ u v : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hzu : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → u z = 0)
    (hzv : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → v z = 0)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ thinBallAt R o, ∀ w,
      0 ≤ quaternionForm (thinQuaternionHessian (u+t•v) z) w) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => thinFunctionalAt R o ρ (u+t•v)) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (0 : ℝ) 1)
    (fun t _ => (hasDerivAt_thinFunctionalAt_line hR o hρ hu hv hzu hzv t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_thinFunctionalAt_line hR o hρ hu hv hzu hzv t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_thinLineDerivative hR o hρ hu hv t).hasDerivWithinAt)
  intro t ht
  have htuv : ContDiff ℝ 3 (u+t•v) := hu.add (contDiff_const.smul hv)
  have he := thinCofactor_energy_nonneg hR o htuv (hv.of_le (by norm_num))
    hzv (hpos t (interior_subset ht))
  simp only [thinQuaternionHessian_affine (hu.of_le (by norm_num))
    (hv.of_le (by norm_num)), neg_mul, integral_neg] at he
  exact neg_nonneg.mp he

theorem thinHessian_segment_nonneg {m : ℕ} {u v : ThinSpace m → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) {z : ThinSpace m}
    (hpu : ∀ w, 0 ≤ quaternionForm (thinQuaternionHessian u z) w)
    (hpv : ∀ w, 0 ≤ quaternionForm (thinQuaternionHessian v z) w)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (w : Fin m → Quaternion ℝ) :
    0 ≤ quaternionForm (thinQuaternionHessian (u+t•(v-u)) z) w := by
  have he : u+t•(v-u) = (1-t)•u+t•v := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have htu : ContDiff ℝ 2 ((1-t)•u) := contDiff_const.smul hu
  have htv : ContDiff ℝ 2 (t•v) := contDiff_const.smul hv
  rw [he, thinQuaternionHessian_add htu htv, thinQuaternionHessian_smul,
    thinQuaternionHessian_smul, quaternionForm_add, quaternionForm_smul, quaternionForm_smul]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hpu w)) (mul_nonneg ht.1 (hpv w))

theorem thinFunctional_supporting_inequality {m : ℕ} {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ u v : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hzu : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → u z = 0)
    (hzv : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → v z = 0)
    (hpu : ∀ z ∈ thinBallAt R o, ∀ w, 0 ≤ quaternionForm (thinQuaternionHessian u z) w)
    (hpv : ∀ z ∈ thinBallAt R o, ∀ w, 0 ≤ quaternionForm (thinQuaternionHessian v z) w) :
    thinFunctionalAt R o ρ v - thinFunctionalAt R o ρ u ≤
      ∫ z in thinBallAt R o, (v z-u z)*(mooreDet m (thinQuaternionHessian u z)-ρ z) := by
  have hzw : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → (v-u) z = 0 := by
    intro z hz
    simp [hzu z hz, hzv z hz]
  have hc := thinFunctional_concave_line hR o hρ hu (hv.sub hu) hzu hzw
    (fun t ht z hz => thinHessian_segment_nonneg (hu.of_le (by norm_num))
      (hv.of_le (by norm_num)) (hpu z hz) (hpv z hz) ht)
  have hs := hc.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) zero_lt_one
    (hasDerivAt_thinFunctionalAt_line hR o hρ hu (hv.sub hu) hzu hzw 0)
  have he : u+(v-u) = v := by abel
  simp only [slope, sub_zero, inv_one, one_smul, vsub_eq_sub, zero_smul,
    add_zero, thinLineDerivative] at hs
  change thinFunctionalAt R o ρ (u+(v-u)) - thinFunctionalAt R o ρ u ≤
    ∫ z in thinBallAt R o, (v z-u z)*(mooreDet m (thinQuaternionHessian u z)-ρ z) at hs
  rwa [he] at hs

theorem thinFunctional_maximized_of_detEquation {m : ℕ} {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ u v : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hzu : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → u z = 0)
    (hzv : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → v z = 0)
    (hpu : ∀ z ∈ thinBallAt R o, ∀ w, 0 ≤ quaternionForm (thinQuaternionHessian u z) w)
    (hpv : ∀ z ∈ thinBallAt R o, ∀ w, 0 ≤ quaternionForm (thinQuaternionHessian v z) w)
    (hEq : ∀ z ∈ thinBallAt R o, mooreDet m (thinQuaternionHessian u z) = ρ z) :
    thinFunctionalAt R o ρ v ≤ thinFunctionalAt R o ρ u := by
  have h := thinFunctional_supporting_inequality hR o hρ hu hv hzu hzv hpu hpv
  have hz : (∫ z in thinBallAt R o, (v z-u z)*(mooreDet m (thinQuaternionHessian u z)-ρ z)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro z hz
    rw [hEq z hz, sub_self, mul_zero]
  rw [hz] at h
  exact sub_nonpos.mp h

end KakeyaSharp

