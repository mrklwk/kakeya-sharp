/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinDeterminant

@[expose] public section

/-! The actual determinant energy density on the Euclidean unit ball. -/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff
namespace KakeyaSharp
open KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore

def thinBall (m : ℕ) : Set (ThinSpace m) :=
  {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < 1}

def thinClosedBall (m : ℕ) : Set (ThinSpace m) :=
  {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1}

def thinEnergyDensity {m : ℕ} (η : ℝ) (z : ThinSpace m) : ℝ :=
  (-thinProfile η z) * mooreDet m (thinQuaternionHessian (thinProfile η) z)

def thinEnergy (m : ℕ) (η : ℝ) : ℝ :=
  ∫ z in thinBall m, thinEnergyDensity η z

theorem thinBall_measurable (m : ℕ) : MeasurableSet (thinBall m) := by
  exact measurableSet_lt (by fun_prop) measurable_const

theorem thinClosedBall_compact (m : ℕ) : IsCompact (thinClosedBall m) := by
  have hc : IsClosed (thinClosedBall m) := isClosed_le (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : ThinSpace m) 1).of_isClosed_subset hc
  intro z hz
  change ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1 at hz
  have hx : ‖z.1‖ ≤ 1 := by nlinarith [sq_nonneg ‖z.2‖, norm_nonneg z.1]
  have hp : ‖z.2‖ ≤ 1 := by nlinarith [sq_nonneg ‖z.1‖, norm_nonneg z.2]
  simpa [mem_closedBall, dist_zero_right, Prod.norm_def] using max_le hx hp

theorem continuous_mooreDet (m : ℕ) :
    Continuous (fun A : Matrix (Fin m) (Fin m) (Quaternion ℝ) => mooreDet m A) := by
  have he (i j : Fin m × Fin 2) : Continuous
      (fun A : Matrix (Fin m) (Fin m) (Quaternion ℝ) => skewComplexify A i j) := by
    change Continuous (fun A : Matrix (Fin m) (Fin m) (Quaternion ℝ) =>
      skewQuaternionEntryCLM i.2 j.2 (A i.1 j.1))
    exact (skewQuaternionEntryCLM i.2 j.2).continuous.comp (by fun_prop)
  unfold mooreDet pfaffian
  fun_prop

theorem thinQuaternionHessian_continuousAt {m : ℕ} {f : ThinSpace m → ℝ}
    {z : ThinSpace m} (hf : ContDiffAt ℝ 3 f z) :
    ContinuousAt (thinQuaternionHessian f) z := by
  have hD := ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).continuousAt
  have hH (i j : Fin m × Fin 3) : ContinuousAt
      (fun y => fderiv ℝ (fderiv ℝ f) y (thinDirection i.1 i.2) (thinDirection j.1 j.2)) z :=
    (hD.clm_apply continuousAt_const).clm_apply continuousAt_const
  unfold thinQuaternionHessian hessianMap thinRealHessian
  fun_prop

theorem thinEnergyDensity_continuousOn {m : ℕ} {η : ℝ} (hη : 0 < η) :
    ContinuousOn (thinEnergyDensity η : ThinSpace m → ℝ) (thinClosedBall m) := by
  intro z hz
  have hs := thinProfile_smooth hη hz
  have hH := thinQuaternionHessian_continuousAt (hs.of_le (by norm_num : (3 : ℕ∞ω) ≤ ∞))
  exact (hs.continuousAt.neg.mul ((continuous_mooreDet m).continuousAt.comp hH)).continuousWithinAt

theorem thinEnergyDensity_integrableOn {m : ℕ} {η : ℝ} (hη : 0 < η) :
    IntegrableOn (thinEnergyDensity η : ThinSpace m → ℝ) (thinBall m) := by
  exact ((thinEnergyDensity_continuousOn hη).integrableOn_compact
    (thinClosedBall_compact m)).mono_set (by
      intro z hz
      change ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < 1 at hz
      exact hz.le)

end KakeyaSharp
