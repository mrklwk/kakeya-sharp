/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinVariation
public import KakeyaSharp.Moore.CofactorPositive

@[expose] public section

/-! The second variation and its sign for the actual three-slot energy. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Matrix.Norms.Elementwise

def thinQuaternionGradient {m : ℕ} (v : ThinSpace m → ℝ) (z : ThinSpace m) :
    Fin m → Quaternion ℝ :=
  gradientMap threeSlots (fun p => fderiv ℝ v z (thinDirection p.1 p.2))

theorem thinCofactor_energy_identity {m : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {u v : ThinSpace m → ℝ} (hu : ContDiff ℝ 3 u)
    (hv : ContDiff ℝ 2 v)
    (hzv : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → v z = 0) :
    (∫ z in thinBallAt R o, (-v z)*mooreDifferential m
      (thinQuaternionHessian u z) (thinQuaternionHessian v z)) =
    ∫ z in thinBallAt R o,
      quaternionForm (thinCofactor u z) (thinQuaternionGradient v z) := by
  let : (volume : Measure (ThinSpace m)).IsAddHaarMeasure := by
    change ((volume : Measure (Space m)).prod (volume : Measure (ThinTransverseSpace m))).IsAddHaarMeasure
    infer_instance
  have h := Green.moore_cofactor_green_bounded threeSlots
    (fun p => thinDirection p.1 p.2) (thinBallAt_isOpen R o)
    (thinBallAt_bounded hR.le o) (thinBallAt_null_frontier R o) hu
    (hv.of_le (by norm_num)) hv
    (fun z hz => hzv z (thinBallAt_frontier_subset R o hz))
  have he (z : ThinSpace m) :
      (∑ p, ∑ q, realCoefficients threeSlots (thinCofactor u z) p q *
        fderiv ℝ v z (thinDirection p.1 p.2) * fderiv ℝ v z (thinDirection q.1 q.2)) =
      quaternionForm (thinCofactor u z) (thinQuaternionGradient v z) := by
    simp_rw [mul_assoc]
    exact Green.realCoefficients_quadratic _ threeSlots _
  change (∫ z in thinBallAt R o, v z*mooreDifferential m
      (thinQuaternionHessian u z) (thinQuaternionHessian v z)) =
    -(∫ z in thinBallAt R o, ∑ p, ∑ q, realCoefficients threeSlots (thinCofactor u z) p q *
      fderiv ℝ v z (thinDirection p.1 p.2) * fderiv ℝ v z (thinDirection q.1 q.2)) at h
  simp_rw [he] at h
  simp_rw [neg_mul]
  rw [integral_neg, h, neg_neg]

theorem thinCofactor_energy_nonneg {m : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {u v : ThinSpace m → ℝ} (hu : ContDiff ℝ 3 u)
    (hv : ContDiff ℝ 2 v)
    (hzv : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → v z = 0)
    (hpos : ∀ z ∈ thinBallAt R o, ∀ w, 0 ≤ quaternionForm (thinQuaternionHessian u z) w) :
    0 ≤ ∫ z in thinBallAt R o, (-v z)*mooreDifferential m
      (thinQuaternionHessian u z) (thinQuaternionHessian v z) := by
  rw [thinCofactor_energy_identity hR o hu hv hzv]
  apply setIntegral_nonneg (thinBallAt_measurable R o)
  intro z hz
  exact mooreCofactor_quaternionForm_nonneg _ (thinQuaternionHessian_isHermitian
    (hu.contDiffAt.of_le (by norm_num))) (hpos z hz) _

def thinLineDerivative {m : ℕ} (R : ℝ) (o : ThinSpace m)
    (ρ u v : ThinSpace m → ℝ) (t : ℝ) : ℝ :=
  ∫ z in thinBallAt R o, v z * (mooreDet m
    (thinQuaternionHessian u z + t • thinQuaternionHessian v z) - ρ z)

theorem hasDerivAt_thinFunctionalAt_line {m : ℕ} {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ u v : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hzu : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → u z = 0)
    (hzv : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → v z = 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => thinFunctionalAt R o ρ (u+s•v))
      (thinLineDerivative R o ρ u v t) t := by
  have ht : ContDiff ℝ 3 (u+t•v) := hu.add (contDiff_const.smul hv)
  have hzt : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → (u+t•v) z = 0 := by
    intro z hz
    simp [hzu z hz, hzv z hz]
  have h := hasDerivAt_thinFunctionalAt hR o hρ ht hv hzt hzv
  have h' : HasDerivAt (fun s : ℝ => thinFunctionalAt R o ρ (u+t•v+s•v))
      (thinLineDerivative R o ρ u v t) (t-t) := by
    simpa only [sub_self, thinLineDerivative, thinQuaternionHessian_affine
      (hu.of_le (by norm_num)) (hv.of_le (by norm_num))] using h
  have hs := h'.comp_sub_const t t
  have he (s : ℝ) : u+t•v+(s-t)•v = u+s•v := by
    rw [add_assoc, ← add_smul]
    congr 2
    ring
  simpa only [he] using hs

set_option maxHeartbeats 800000 in
theorem hasDerivAt_thinLineDerivative {m : ℕ} {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ u v : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) (t : ℝ) :
    HasDerivAt (thinLineDerivative R o ρ u v)
      (∫ z in thinBallAt R o, v z * mooreDifferential m
        (thinQuaternionHessian u z + t • thinQuaternionHessian v z)
        (thinQuaternionHessian v z)) t := by
  let F : ℝ × ThinSpace m → ℝ := fun p =>
    v p.2 * mooreDet m (thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2)
  let F' : ℝ × ThinSpace m → ℝ := fun p =>
    v p.2 * mooreDifferential m (thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2)
      (thinQuaternionHessian v p.2)
  have hA : Continuous (fun p : ℝ × ThinSpace m =>
      thinQuaternionHessian u p.2 + p.1 • thinQuaternionHessian v p.2) :=
    ((thinHessian_continuous hu).comp continuous_snd).add
      (continuous_fst.smul ((thinHessian_continuous hv).comp continuous_snd))
  have hF : Continuous F :=
    (hv.continuous.comp continuous_snd).mul ((KakeyaSharp.continuous_mooreDet m).comp hA)
  have hF' : Continuous F' :=
    (hv.continuous.comp continuous_snd).mul (continuous_thinDifferential_affine hu hv)
  have hd (s : ℝ) (z : ThinSpace m) :
      HasDerivAt (fun r => F (r,z)) (F' (s,z)) s := by
    exact (hasDerivAt_mooreDet_affine (thinQuaternionHessian u z)
      (thinQuaternionHessian v z) s).const_mul (v z)
  have h := hasDerivAt_setIntegral_compact (μ := volume) (thinBallAt_measurable R o)
    (thinClosedBallAt_compact hR.le o)
    (fun z hz => show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le) hF hF' hd t
  have hivρ : IntegrableOn (fun z => v z*ρ z) (thinBallAt R o) :=
    ((hv.continuous.continuousOn.mul hρ).integrableOn_compact
      (thinClosedBallAt_compact hR.le o)).mono_set
      (fun z hz => show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)
  have he (s : ℝ) : thinLineDerivative R o ρ u v s =
      (∫ z in thinBallAt R o, F (s,z)) - ∫ z in thinBallAt R o, v z*ρ z := by
    have hi : IntegrableOn (fun z => F (s,z)) (thinBallAt R o) :=
      continuous_integrableOn_thinBallAt hR o (hF.comp (continuous_const.prodMk continuous_id))
    simp only [thinLineDerivative, mul_sub]
    exact integral_sub hi hivρ
  simpa only [← he] using h.sub_const (∫ z in thinBallAt R o, v z*ρ z)

end KakeyaSharp

