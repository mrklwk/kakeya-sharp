/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinVariational

@[expose] public section

/-! Spatial translation and dilation for the three-slot determinant energy. -/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff
namespace KakeyaSharp
open KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore

def rescaleTest {m : ℕ} (R : ℝ) (o : ThinSpace m) (f : ThinSpace m → ℝ) : ThinSpace m → ℝ :=
  fun z => f (R⁻¹ • (z - o))

def thinBallAt {m : ℕ} (R : ℝ) (o : ThinSpace m) : Set (ThinSpace m) :=
  {z | ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 < R ^ 2}

def thinClosedBallAt {m : ℕ} (R : ℝ) (o : ThinSpace m) : Set (ThinSpace m) :=
  {z | ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 ≤ R ^ 2}

def determinantEnergyAt {m : ℕ} (R : ℝ) (o : ThinSpace m) (f : ThinSpace m → ℝ) : ℝ :=
  ∫ z in thinBallAt R o, (-f z) * mooreDet m (thinQuaternionHessian f z)

def thinFunctionalAt {m : ℕ} (R : ℝ) (o : ThinSpace m) (μ f : ThinSpace m → ℝ) : ℝ :=
  (∫ z in thinBallAt R o, (-f z) * μ z) - determinantEnergyAt R o f / ((m : ℝ) + 1)

theorem thinQuaternionHessian_comp_smul {m : ℕ} (c : ℝ) (f : ThinSpace m → ℝ)
    (z : ThinSpace m) :
    thinQuaternionHessian (fun y => f (c • y)) z = c ^ 2 • thinQuaternionHessian f (c • z) := by
  have hd : fderiv ℝ (fun y => f (c • y)) =
      c • (fun y => fderiv ℝ f (c • y)) := by
    funext y
    exact fderiv_comp_smul c
  have hh : thinRealHessian (fun y => f (c • y)) z =
      c ^ 2 • thinRealHessian f (c • z) := by
    ext i j
    change (fderiv ℝ (fderiv ℝ (fun y => f (c • y))) z
      (thinDirection i.1 i.2)) (thinDirection j.1 j.2) =
      c ^ 2 * (thinRealHessian f (c • z) i j)
    rw [hd, fderiv_const_smul_field (𝕜 := ℝ) (f := fun y => fderiv ℝ f (c • y)) c]
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
    rw [fderiv_comp_smul (f := fderiv ℝ f) c]
    simp [thinRealHessian, pow_two, mul_assoc]
  unfold thinQuaternionHessian
  rw [hh, hessianMap_smul]

theorem thinQuaternionHessian_comp_sub {m : ℕ} (o : ThinSpace m) (f : ThinSpace m → ℝ)
    (z : ThinSpace m) :
    thinQuaternionHessian (fun y => f (y - o)) z = thinQuaternionHessian f (z - o) := by
  have hd : fderiv ℝ (fun y => f (y - o)) = fun y => fderiv ℝ f (y - o) := by
    funext y
    exact fderiv_comp_sub o
  unfold thinQuaternionHessian
  congr 1
  ext i j
  unfold thinRealHessian
  rw [hd, fderiv_comp_sub]

theorem thinQuaternionHessian_rescale {m : ℕ} (R : ℝ) (o : ThinSpace m)
    (f : ThinSpace m → ℝ) (z : ThinSpace m) :
    thinQuaternionHessian (rescaleTest R o f) z =
      R⁻¹ ^ 2 • thinQuaternionHessian f (R⁻¹ • (z - o)) := by
  exact (thinQuaternionHessian_comp_sub o (fun y => f (R⁻¹ • y)) z).trans
    (thinQuaternionHessian_comp_smul R⁻¹ f (z - o))

theorem scaled_norm_sum {m : ℕ} {R : ℝ} (hR : 0 < R) (o z : ThinSpace m) :
    ‖(R⁻¹ • (z - o)).1‖ ^ 2 + ‖(R⁻¹ • (z - o)).2‖ ^ 2 =
      (‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2) / R ^ 2 := by
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  ring

theorem thinBallAt_mem {m : ℕ} {R : ℝ} (hR : 0 < R) (o z : ThinSpace m) :
    z ∈ thinBallAt R o ↔ R⁻¹ • (z - o) ∈ thinBall m := by
  change ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 < R ^ 2 ↔
    ‖(R⁻¹ • (z - o)).1‖ ^ 2 + ‖(R⁻¹ • (z - o)).2‖ ^ 2 < 1
  rw [scaled_norm_sum hR, div_lt_one (sq_pos_of_pos hR)]

theorem thinClosedBallAt_mem {m : ℕ} {R : ℝ} (hR : 0 < R) (o z : ThinSpace m) :
    z ∈ thinClosedBallAt R o ↔ R⁻¹ • (z - o) ∈ thinClosedBall m := by
  change ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 ≤ R ^ 2 ↔
    ‖(R⁻¹ • (z - o)).1‖ ^ 2 + ‖(R⁻¹ • (z - o)).2‖ ^ 2 ≤ 1
  rw [scaled_norm_sum hR, div_le_one (sq_pos_of_pos hR)]

theorem thinBallAt_measurable {m : ℕ} (R : ℝ) (o : ThinSpace m) :
    MeasurableSet (thinBallAt R o) := measurableSet_lt (by fun_prop) measurable_const

theorem integral_rescale {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    (f : ThinSpace m → ℝ) :
    (∫ z in thinBallAt R o, rescaleTest R o f z) = R ^ (3 * m) * ∫ z in thinBall m, f z := by
  let : (volume : Measure (ThinSpace m)).IsAddHaarMeasure := by
    change ((volume : Measure (Space m)).prod (volume : Measure (ThinTransverseSpace m))).IsAddHaarMeasure
    infer_instance
  rw [← integral_indicator (thinBallAt_measurable R o)]
  have he : (thinBallAt R o).indicator (rescaleTest R o f) =
      fun z => (thinBall m).indicator f (R⁻¹ • (z - o)) := by
    funext z
    by_cases hz : z ∈ thinBallAt R o
    · simp [hz, (thinBallAt_mem hR o z).mp hz, rescaleTest]
    · have hz' := mt (thinBallAt_mem hR o z).mpr hz
      simp [hz, hz']
  have htranslate : (∫ z : ThinSpace m, (thinBall m).indicator f (R⁻¹ • (z - o))) =
      ∫ z : ThinSpace m, (thinBall m).indicator f (R⁻¹ • z) := by
    simpa only [sub_eq_neg_add] using integral_add_left_eq_self
      (μ := (volume : Measure (ThinSpace m)))
      (fun z => (thinBall m).indicator f (R⁻¹ • z)) (-o)
  rw [he, htranslate,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (ThinSpace m)) _ hR.le,
    integral_indicator (thinBall_measurable m)]
  have hdim : Module.finrank ℝ (ThinSpace m) = 3 * m := by
    simp [ThinSpace, Space, ThinTransverseSpace]
    omega
  rw [hdim]
  rfl

theorem determinantEnergyAt_rescale {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    (f : ThinSpace m → ℝ) :
    determinantEnergyAt R o (rescaleTest R o f) = R ^ m * determinantEnergy f := by
  unfold determinantEnergyAt
  simp_rw [thinQuaternionHessian_rescale, mooreDet_smul]
  have he (z : ThinSpace m) : -(rescaleTest R o f z) *
      ((R⁻¹ ^ 2) ^ m * mooreDet m (thinQuaternionHessian f (R⁻¹ • (z - o)))) =
      (R⁻¹ ^ 2) ^ m * rescaleTest R o
        (fun y => (-f y) * mooreDet m (thinQuaternionHessian f y)) z := by
    unfold rescaleTest
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_rescale hR]
  have hp : (R⁻¹ ^ 2) ^ m * R ^ (3 * m) = R ^ m := by
    rw [← pow_mul, inv_pow]
    have he : 3 * m = 2 * m + m := by omega
    rw [he, pow_add]
    field_simp [hR.ne']
  rw [← mul_assoc, hp]
  rfl

end KakeyaSharp
