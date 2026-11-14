/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinCofactor
public import KakeyaSharp.CompactVariation

@[expose] public section

/-! First variations of the actual determinant energy and source functional.
The hypotheses here require globally C³ functions with zero boundary values;
the admissible class defined earlier only requires smoothness near the closed ball. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Matrix.Norms.Elementwise

theorem thinQuaternionHessian_add {m : ℕ} {u v : ThinSpace m → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (z : ThinSpace m) :
    thinQuaternionHessian (u + v) z =
      thinQuaternionHessian u z + thinQuaternionHessian v z := by
  have hd : fderiv ℝ (u+v) = fderiv ℝ u + fderiv ℝ v :=
    funext (fun x => fderiv_add (hu.differentiable (by norm_num) x)
      (hv.differentiable (by norm_num) x))
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdv := (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hh : thinRealHessian (u+v) z = thinRealHessian u z + thinRealHessian v z := by
    ext p q
    unfold thinRealHessian
    rw [hd, fderiv_add (hdu z) (hdv z)]
    rfl
  unfold thinQuaternionHessian
  rw [hh, hessianMap_add]

theorem thinQuaternionHessian_affine {m : ℕ} {u v : ThinSpace m → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (t : ℝ) (z : ThinSpace m) :
    thinQuaternionHessian (u + t • v) z =
      thinQuaternionHessian u z + t • thinQuaternionHessian v z := by
  have htv : ContDiff ℝ 2 (t • v) := by
    exact contDiff_const.smul hv
  rw [thinQuaternionHessian_add hu htv, thinQuaternionHessian_smul]

theorem thinHessian_continuous {m : ℕ} {u : ThinSpace m → ℝ}
    (hu : ContDiff ℝ 3 u) : Continuous (thinQuaternionHessian u) :=
  (Green.contDiff_directionalHessian_one threeSlots (fun p => thinDirection p.1 p.2) hu).continuous

theorem continuous_thinDifferential_affine {m : ℕ} {u v : ThinSpace m → ℝ}
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) :
    Continuous (fun p : ℝ × ThinSpace m =>
      mooreDifferential m (thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2)
        (thinQuaternionHessian v p.2)) := by
  have hA : Continuous (fun p : ℝ × ThinSpace m =>
      thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2) :=
    ((thinHessian_continuous hu).comp continuous_snd).add
      (continuous_fst.smul ((thinHessian_continuous hv).comp continuous_snd))
  have hC := (contDiff_mooreCofactor m 0).continuous.comp hA
  have he (p : ℝ × ThinSpace m) :
      mooreDifferential m (thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2)
        (thinQuaternionHessian v p.2) =
      realTrace (mooreCofactor m (thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2) *
        thinQuaternionHessian v p.2) :=
    (mooreCofactor_pairing m _ _ (thinQuaternionHessian_isHermitian
      (hv.contDiffAt.of_le (by norm_num)))).symm
  simp_rw [he]
  have hV := (thinHessian_continuous hv).comp (continuous_snd : Continuous (Prod.snd : ℝ × ThinSpace m → _))
  unfold realTrace Matrix.trace Matrix.diag
  simp only [quaternion_re_sum]
  apply continuous_finsetSum
  intro i _
  simp only [Matrix.mul_apply, quaternion_re_sum]
  apply continuous_finsetSum
  intro j _
  exact Quaternion.continuous_re.comp
    (((continuous_apply j).comp ((continuous_apply i).comp hC)).mul
      ((continuous_apply i).comp ((continuous_apply j).comp hV)))

theorem continuous_integrableOn_thinBallAt {m : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {f : ThinSpace m → ℝ} (hf : Continuous f) :
    IntegrableOn f (thinBallAt R o) :=
  (hf.continuousOn.integrableOn_compact (thinClosedBallAt_compact hR.le o)).mono_set
    (fun z hz => show ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 ≤ R^2 from hz.le)

set_option maxHeartbeats 800000 in
theorem hasDerivAt_determinantEnergyAt {m : ℕ} {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {u v : ThinSpace m → ℝ}
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hzu : ∀ z, ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 = R^2 → u z = 0)
    (hzv : ∀ z, ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 = R^2 → v z = 0) :
    HasDerivAt (fun t : ℝ => determinantEnergyAt R o (u+t•v))
      (-((m : ℝ)+1) * ∫ z in thinBallAt R o,
        v z * mooreDet m (thinQuaternionHessian u z)) 0 := by
  let F : ℝ × ThinSpace m → ℝ := fun p =>
    (-(u p.2 + p.1*v p.2)) *
      mooreDet m (thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2)
  let F' : ℝ × ThinSpace m → ℝ := fun p =>
    (-v p.2) * mooreDet m (thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2) +
      (-(u p.2 + p.1*v p.2)) *
        mooreDifferential m (thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2)
          (thinQuaternionHessian v p.2)
  have hA : Continuous (fun p : ℝ × ThinSpace m =>
      thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2) :=
    ((thinHessian_continuous hu).comp continuous_snd).add
      (continuous_fst.smul ((thinHessian_continuous hv).comp continuous_snd))
  have hdet := (continuous_mooreDet m).comp hA
  have hF : Continuous F := ((hu.continuous.comp continuous_snd).add
    (continuous_fst.mul (hv.continuous.comp continuous_snd))).neg.mul hdet
  have hF' : Continuous F' :=
    ((hv.continuous.comp continuous_snd).neg.mul hdet).add
      (((hu.continuous.comp continuous_snd).add
        (continuous_fst.mul (hv.continuous.comp continuous_snd))).neg.mul
          (continuous_thinDifferential_affine hu hv))
  have hd (t : ℝ) (z : ThinSpace m) :
      HasDerivAt (fun r => F (r,z)) (F' (t,z)) t := by
    simpa only [F, F', Pi.neg_apply, Pi.mul_apply, id_eq, one_mul] using!
      (((hasDerivAt_id t).mul_const (v z)).const_add (u z)).neg.mul
      (hasDerivAt_mooreDet_affine (thinQuaternionHessian u z) (thinQuaternionHessian v z) t)
  have h := hasDerivAt_setIntegral_compact (μ := volume) (thinBallAt_measurable R o)
    (thinClosedBallAt_compact hR.le o)
    (fun z hz => show ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 ≤ R^2 from hz.le)
    hF hF' hd 0
  have he (t : ℝ) :
      (∫ z in thinBallAt R o, F (t,z)) = determinantEnergyAt R o (u+t•v) := by
    unfold determinantEnergyAt
    simp only [thinQuaternionHessian_affine (hu.of_le (by norm_num))
      (hv.of_le (by norm_num)), Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hdiff : Continuous (fun z => mooreDifferential m (thinQuaternionHessian u z)
      (thinQuaternionHessian v z)) := by
    simpa only [Function.comp_def, zero_smul, add_zero] using (continuous_thinDifferential_affine hu hv).comp
      (continuous_const.prodMk continuous_id : Continuous (fun z : ThinSpace m => ((0 : ℝ),z)))
  have hi₁ : IntegrableOn (fun z => (-v z)*mooreDet m (thinQuaternionHessian u z))
      (thinBallAt R o) := continuous_integrableOn_thinBallAt hR o
    (hv.continuous.neg.mul ((continuous_mooreDet m).comp (thinHessian_continuous hu)))
  have hi₂ : IntegrableOn (fun z => (-u z)*mooreDifferential m
      (thinQuaternionHessian u z) (thinQuaternionHessian v z)) (thinBallAt R o) :=
    continuous_integrableOn_thinBallAt hR o (hu.continuous.neg.mul hdiff)
  have hvalue : (∫ z in thinBallAt R o, F' (0,z)) =
      -((m : ℝ)+1) * ∫ z in thinBallAt R o,
        v z * mooreDet m (thinQuaternionHessian u z) := by
    simp only [F', zero_smul, add_zero, zero_mul]
    rw [integral_add hi₁ hi₂]
    simp_rw [neg_mul]
    rw [integral_neg, integral_neg, thinEnergy_linearization hR o hu
      (hv.of_le (by norm_num)) hzu hzv]
    ring
  simpa only [he, hvalue] using h


theorem hasDerivAt_thinFunctionalAt {m : ℕ} {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ u v : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hzu : ∀ z, ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 = R^2 → u z = 0)
    (hzv : ∀ z, ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 = R^2 → v z = 0) :
    HasDerivAt (fun t : ℝ => thinFunctionalAt R o ρ (u+t•v))
      (∫ z in thinBallAt R o, v z * (mooreDet m (thinQuaternionHessian u z) - ρ z)) 0 := by
  have hiu : IntegrableOn (fun z => (-u z)*ρ z) (thinBallAt R o) :=
    ((hu.continuous.continuousOn.neg.mul hρ).integrableOn_compact
      (thinClosedBallAt_compact hR.le o)).mono_set
        (fun z hz => show ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 ≤ R^2 from hz.le)
  have hiv : IntegrableOn (fun z => v z*ρ z) (thinBallAt R o) :=
    ((hv.continuous.continuousOn.mul hρ).integrableOn_compact
      (thinClosedBallAt_compact hR.le o)).mono_set
        (fun z hz => show ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 ≤ R^2 from hz.le)
  have hs (t : ℝ) :
      (∫ z in thinBallAt R o, (-(u+t•v) z)*ρ z) =
      (∫ z in thinBallAt R o, (-u z)*ρ z) -
        t * ∫ z in thinBallAt R o, v z*ρ z := by
    calc
      _ = ∫ z in thinBallAt R o, (-u z)*ρ z - t*(v z*ρ z) := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      _ = _ := by rw [integral_sub hiu (hiv.const_mul t), integral_const_mul]
  have hsource :
      HasDerivAt (fun t : ℝ => ∫ z in thinBallAt R o, (-(u+t•v) z)*ρ z)
        (-(∫ z in thinBallAt R o, v z*ρ z)) 0 := by
    simp_rw [hs]
    simpa only [Pi.sub_apply, Pi.sub_def, id_eq, one_mul, zero_sub] using!
      (hasDerivAt_const (0 : ℝ) (∫ z in thinBallAt R o, (-u z)*ρ z)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (∫ z in thinBallAt R o, v z*ρ z))
  have henergy := hasDerivAt_determinantEnergyAt hR o hu hv hzu hzv
  have h := hsource.sub (henergy.div_const ((m : ℝ)+1))
  have hid : IntegrableOn (fun z => v z*mooreDet m (thinQuaternionHessian u z))
      (thinBallAt R o) := continuous_integrableOn_thinBallAt hR o
    (hv.continuous.mul ((continuous_mooreDet m).comp (thinHessian_continuous hu)))
  have hvalue :
      -(∫ z in thinBallAt R o, v z*ρ z) -
        (-((m : ℝ)+1) * ∫ z in thinBallAt R o, v z*mooreDet m (thinQuaternionHessian u z)) /
          ((m : ℝ)+1) =
      ∫ z in thinBallAt R o, v z*(mooreDet m (thinQuaternionHessian u z)-ρ z) := by
    simp_rw [mul_sub]
    rw [integral_sub hid hiv]
    have hm : (m : ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring
  simpa only [thinFunctionalAt, hvalue, Pi.sub_def] using! h

theorem thinFunctional_stationary_of_detEquation {m : ℕ} {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ u v : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hzu : ∀ z, ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 = R^2 → u z = 0)
    (hzv : ∀ z, ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 = R^2 → v z = 0)
    (hEq : ∀ z ∈ thinBallAt R o, mooreDet m (thinQuaternionHessian u z) = ρ z) :
    HasDerivAt (fun t : ℝ => thinFunctionalAt R o ρ (u+t•v)) 0 0 := by
  have h := hasDerivAt_thinFunctionalAt hR o hρ hu hv hzu hzv
  have hz : (∫ z in thinBallAt R o, v z*(mooreDet m (thinQuaternionHessian u z)-ρ z)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro z hz
    rw [hEq z hz, sub_self, mul_zero]
  rwa [hz] at h

end KakeyaSharp

