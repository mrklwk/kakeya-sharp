/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.SpatialScaling

@[expose] public section

/-! The variational functional and admissible tests on a translated ball. -/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff
namespace KakeyaSharp
open KakeyaSharp.QuaternionAlgebra

def rescaleSource {m : ℕ} (R : ℝ) (o : ThinSpace m) (μ : ThinSpace m → ℝ) : ThinSpace m → ℝ :=
  fun z => R ^ (2 * m) * μ (o + R • z)

def ThinAdmissibleAt {m : ℕ} (R : ℝ) (o : ThinSpace m) (f : ThinSpace m → ℝ) : Prop :=
  (∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 3 f z) ∧
  (∀ z : ThinSpace m, ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 = R ^ 2 → f z = 0) ∧
  (∀ z ∈ thinClosedBallAt R o, ∀ w : Fin m → Quaternion ℝ,
    0 ≤ quaternionForm (thinQuaternionHessian f z) w)

theorem ThinAdmissible.rescale {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {f : ThinSpace m → ℝ} (hf : ThinAdmissible f) :
    ThinAdmissibleAt R o (rescaleTest R o f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact (hf.1 _ ((thinClosedBallAt_mem hR o z).mp hz)).comp z (by fun_prop)
  · intro z hz
    apply hf.2.1
    rw [scaled_norm_sum hR, hz, div_self (sq_pos_of_pos hR).ne']
  · intro z hz w
    rw [thinQuaternionHessian_rescale, quaternionForm_smul]
    exact mul_nonneg (sq_nonneg _) (hf.2.2 _ ((thinClosedBallAt_mem hR o z).mp hz) w)

theorem thinFunctionalAt_rescale {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    (μ f : ThinSpace m → ℝ) :
    thinFunctionalAt R o μ (rescaleTest R o f) =
      R ^ m * thinFunctional (rescaleSource R o μ) f := by
  unfold thinFunctionalAt thinFunctional
  rw [determinantEnergyAt_rescale hR]
  have he : (fun z => (-rescaleTest R o f z) * μ z) =
      rescaleTest R o (fun y => (-f y) * μ (o + R • y)) := by
    funext z
    simp [rescaleTest, smul_smul, hR.ne']
  rw [he, integral_rescale hR]
  have he' (z : ThinSpace m) : (-f z) * rescaleSource R o μ z =
      R ^ (2 * m) * ((-f z) * μ (o + R • z)) := by unfold rescaleSource; ring
  simp_rw [he', integral_const_mul]
  rw [show 3 * m = m + 2 * m by omega, pow_add]
  ring

theorem rescaleSource_continuousOn {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {μ : ThinSpace m → ℝ} (hμ : ContinuousOn μ (thinClosedBallAt R o)) :
    ContinuousOn (rescaleSource R o μ) (thinClosedBall m) := by
  apply continuousOn_const.mul (hμ.comp (by fun_prop) ?_)
  intro z hz
  apply (thinClosedBallAt_mem hR o _).mpr
  simpa [smul_smul, hR.ne'] using hz

def thinCoreAt {m : ℕ} (R ε : ℝ) (o : ThinSpace m) : Set (ThinSpace m) :=
  ball o.1 (R / 2) ×ˢ ball o.2 ε

theorem thinCoreAt_of_unit {m : ℕ} {R ε : ℝ} (hR : 0 < R) (o z : ThinSpace m)
    (hz : z ∈ thinCore m (ε / R)) : o + R • z ∈ thinCoreAt R ε o := by
  have hx : ‖z.1‖ < 1 / 2 := by simpa [mem_ball, dist_zero_right] using hz.1
  have hp : ‖z.2‖ < ε / R := by simpa [mem_ball, dist_zero_right] using hz.2
  change dist (o + R • z).1 o.1 < R / 2 ∧ dist (o + R • z).2 o.2 < ε
  simp only [dist_eq_norm, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  constructor
  · nlinarith
  · nlinarith [(lt_div_iff₀ hR).mp hp]

theorem scaled_source_power {m : ℕ} (hm : 1 ≤ m) {R a : ℝ} (hR : 0 < R) (ha : 0 ≤ a) :
    (R ^ (2 * m) * a) ^ (((m : ℝ) + 1) / m) =
      R ^ (2 * m + 2) * a ^ (((m : ℝ) + 1) / m) := by
  rw [Real.mul_rpow (pow_nonneg hR.le _) ha]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le, ← Real.rpow_natCast]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  push_cast
  field_simp

/-- A smooth admissible test with the full dimensional and logarithmic thin-source bound. -/
theorem thinSource_variational_lower_scaled {m : ℕ} (hm : 1 ≤ m) {R ε a : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (hεR : ε ≤ R / 10) (ha : 0 ≤ a)
    (o : ThinSpace m) {μ : ThinSpace m → ℝ}
    (hμ : ContinuousOn μ (thinClosedBallAt R o))
    (hμ0 : ∀ z ∈ thinBallAt R o, 0 ≤ μ z)
    (hμa : ∀ z ∈ thinCoreAt R ε o, a ≤ μ z) :
    ∃ v : ThinSpace m → ℝ, ThinAdmissibleAt R o v ∧
      thinLowerConstant m * R ^ m * ε ^ (2 * m + 2) *
        a ^ (((m : ℝ) + 1) / m) * Real.log (R / ε) ≤ thinFunctionalAt R o μ v := by
  have hη : 0 < ε / R := div_pos hε hR
  have hη10 : ε / R ≤ 1 / 10 := (div_le_iff₀ hR).mpr (by linarith)
  have hμR := rescaleSource_continuousOn hR o hμ
  have hμR0 : ∀ z ∈ thinBall m, 0 ≤ rescaleSource R o μ z := by
    intro z hz
    apply mul_nonneg (pow_nonneg hR.le _)
    apply hμ0
    apply (thinBallAt_mem hR o _).mpr
    simpa [smul_smul, hR.ne'] using hz
  have hμRa : ∀ z ∈ thinCore m (ε / R), R ^ (2 * m) * a ≤ rescaleSource R o μ z := by
    intro z hz
    exact mul_le_mul_of_nonneg_left (hμa _ (thinCoreAt_of_unit hR o z hz)) (pow_nonneg hR.le _)
  obtain ⟨f, hf, hval⟩ := thinSource_variational_lower hm hη hη10
    (mul_nonneg (pow_nonneg hR.le _) ha) hμR hμR0 hμRa
  refine ⟨rescaleTest R o f, hf.rescale hR o, ?_⟩
  rw [thinFunctionalAt_rescale hR]
  have hh := mul_le_mul_of_nonneg_left hval (pow_nonneg hR.le m)
  apply le_trans _ hh
  apply le_of_eq
  rw [scaled_source_power (show 1 ≤ m by omega) hR ha, div_pow]
  have hlog : 1 / (ε / R) = R / ε := by field_simp
  rw [hlog]
  field_simp

end KakeyaSharp
