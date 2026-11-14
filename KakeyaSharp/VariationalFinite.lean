/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinMaximum

@[expose] public section

/-! Finiteness of the original variational supremum for every continuous source.
This uses the maximum principle and an explicit constant-source quadratic
solution, and does not use nonlinear PDE existence for general sources. -/
noncomputable section
namespace KakeyaSharp
open Set MeasureTheory KakeyaSharp.Moore
open scoped ContDiff

theorem ThinAdmissibleAt.smul {m : ℕ} {R : ℝ} {o : ThinSpace m}
    {f : ThinSpace m → ℝ} (hf : ThinAdmissibleAt R o f) {c : ℝ} (hc : 0 ≤ c) :
    ThinAdmissibleAt R o (c•f) := by
  refine ⟨fun z hz => contDiffAt_const.smul (hf.1 z hz), ?_, ?_⟩
  · intro z hz
    simp [hf.2.1 z hz]
  · intro z hz w
    rw [thinQuaternionHessian_smul, quaternionForm_smul]
    exact mul_nonneg hc (hf.2.2 z hz w)

theorem ThinAdmissibleAt.functional_mono {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) {o : ThinSpace m} {f ρ σ : ThinSpace m → ℝ}
    (hf : ThinAdmissibleAt R o f)
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hσ : ContinuousOn σ (thinClosedBallAt R o))
    (hρσ : ∀ z ∈ thinBallAt R o, ρ z ≤ σ z) :
    thinFunctionalAt R o ρ f ≤ thinFunctionalAt R o σ f := by
  unfold thinFunctionalAt
  apply sub_le_sub_right
  apply setIntegral_mono_on (hf.source_integrableOn hR hρ)
    (hf.source_integrableOn hR hσ) (thinBallAt_measurable R o)
  intro z hz
  apply mul_le_mul_of_nonneg_left (hρσ z hz)
  exact neg_nonneg.mpr (hf.nonpos hm hR z
    (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le))

theorem thinFunctionalAt_le_constant_quadratic {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ f : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) (hf : ThinAdmissibleAt R o f)
    {c : ℝ} (hc : 0 ≤ c) (hρc : ∀ z ∈ thinBallAt R o, ρ z ≤ c^m) :
    thinFunctionalAt R o ρ f ≤
      thinFunctionalAt R o (fun _ => c^m) (c•thinQuadraticAt R o) := by
  have hq := (thinQuadraticAt_admissible R o).smul hc
  have hEq (z : ThinSpace m) (_ : z ∈ thinBallAt R o) :
      mooreDet m (thinQuaternionHessian (c•thinQuadraticAt R o) z) = c^m := by
    rw [thinQuaternionHessian_smul, thinQuadraticAt_hessian, mooreDet_smul, mooreDet_identity, mul_one]
  exact (hf.functional_mono hm hR hρ continuousOn_const hρc).trans
    (hq.maximizes_of_detEquation hR continuousOn_const hf hEq)

theorem thinVariationalValueAt_nonneg {m : ℕ} (R : ℝ) (o : ThinSpace m)
    (ρ : ThinSpace m → ℝ) : 0 ≤ thinVariationalValueAt R o ρ := by
  have hz : ThinAdmissibleAt R o (0 : ThinSpace m → ℝ) := by
    simpa only [zero_smul] using (thinQuadraticAt_admissible R o).smul (le_refl (0 : ℝ))
  have h := le_iSup (fun f : {f : ThinSpace m → ℝ // ThinAdmissibleAt R o f} =>
    (thinFunctionalAt R o ρ f : EReal)) ⟨0,hz⟩
  simpa [thinVariationalValueAt, thinFunctionalAt, determinantEnergyAt] using h

theorem thinVariationalValueAt_lt_top {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) :
    thinVariationalValueAt R o ρ < ⊤ := by
  obtain ⟨C,hC⟩ := (thinClosedBallAt_compact hR.le o).exists_bound_of_continuousOn hρ
  let c : ℝ := max C 1
  have hc1 : 1 ≤ c := le_max_right _ _
  have hρc : ∀ z ∈ thinBallAt R o, ρ z ≤ c^m := by
    intro z hz
    have hz' : z ∈ thinClosedBallAt R o :=
      show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le
    calc
      ρ z ≤ ‖ρ z‖ := le_abs_self _
      _ ≤ C := hC z hz'
      _ ≤ c := le_max_left _ _
      _ ≤ c^m := le_self_pow₀ hc1 (by omega)
  have hbound : thinVariationalValueAt R o ρ ≤
      (thinFunctionalAt R o (fun _ => c^m) (c•thinQuadraticAt R o) : EReal) := by
    apply iSup_le
    intro f
    exact EReal.coe_le_coe_iff.mpr (thinFunctionalAt_le_constant_quadratic hm hR o hρ f.property
      (zero_le_one.trans hc1) hρc)
  exact hbound.trans_lt (EReal.coe_lt_top _)

theorem thinVariationalValueAt_finite {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) :
    ∃ A : ℝ, 0 ≤ A ∧ thinVariationalValueAt R o ρ = (A : EReal) := by
  have ht := thinVariationalValueAt_lt_top hm hR o hρ
  have hn := thinVariationalValueAt_nonneg R o ρ
  have hb : thinVariationalValueAt R o ρ ≠ ⊥ :=
    (lt_of_lt_of_le (by simp : (⊥ : EReal) < 0) hn).ne'
  have he := EReal.coe_toReal ht.ne hb
  refine ⟨(thinVariationalValueAt R o ρ).toReal, ?_, he.symm⟩
  apply EReal.coe_le_coe_iff.mp
  simpa only [EReal.coe_zero, he] using hn

end KakeyaSharp

