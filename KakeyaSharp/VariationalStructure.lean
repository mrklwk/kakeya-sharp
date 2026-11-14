/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.VariationalFinite

@[expose] public section

/-! Real-valued form of the finite supremum, source comparison, convexity, and
the exact source homogeneity. No PDE solvability is used. -/
noncomputable section
namespace KakeyaSharp
open Set MeasureTheory KakeyaSharp.Moore

def thinValueRealAt {m : ℕ} (R : ℝ) (o : ThinSpace m) (ρ : ThinSpace m → ℝ) : ℝ :=
  (thinVariationalValueAt R o ρ).toReal

theorem coe_thinValueRealAt {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) :
    (thinValueRealAt R o ρ : EReal) = thinVariationalValueAt R o ρ := by
  obtain ⟨A, -, hA⟩ := thinVariationalValueAt_finite hm hR o hρ
  simp [thinValueRealAt, hA]

theorem thinValueRealAt_nonneg {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) : 0 ≤ thinValueRealAt R o ρ := by
  apply EReal.coe_le_coe_iff.mp
  simpa only [EReal.coe_zero, coe_thinValueRealAt hm hR o hρ] using
    thinVariationalValueAt_nonneg R o ρ

theorem ThinAdmissibleAt.functional_le_value {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) {o : ThinSpace m} {ρ f : ThinSpace m → ℝ}
    (hf : ThinAdmissibleAt R o f) (hρ : ContinuousOn ρ (thinClosedBallAt R o)) :
    thinFunctionalAt R o ρ f ≤ thinValueRealAt R o ρ := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_thinValueRealAt hm hR o hρ]
  exact le_iSup (fun g : {g : ThinSpace m → ℝ // ThinAdmissibleAt R o g} =>
    (thinFunctionalAt R o ρ g : EReal)) ⟨f,hf⟩

theorem thinValueRealAt_le {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) {A : ℝ}
    (hA : ∀ f, ThinAdmissibleAt R o f → thinFunctionalAt R o ρ f ≤ A) :
    thinValueRealAt R o ρ ≤ A := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_thinValueRealAt hm hR o hρ]
  exact iSup_le fun f => EReal.coe_le_coe_iff.mpr (hA f f.property)

theorem thinValueRealAt_mono {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {ρ σ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hσ : ContinuousOn σ (thinClosedBallAt R o))
    (hρσ : ∀ z ∈ thinBallAt R o, ρ z ≤ σ z) :
    thinValueRealAt R o ρ ≤ thinValueRealAt R o σ := by
  apply thinValueRealAt_le hm hR o hρ
  intro f hf
  exact (hf.functional_mono hm hR hρ hσ hρσ).trans (hf.functional_le_value hm hR hσ)

theorem thinValueRealAt_zero {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) : thinValueRealAt R o (0 : ThinSpace m → ℝ) = 0 := by
  apply le_antisymm
  · apply thinValueRealAt_le hm hR o (ρ := (0 : ThinSpace m → ℝ)) continuousOn_const
    intro f hf
    have h := thinFunctionalAt_le_constant_quadratic hm hR o
      (ρ := (0 : ThinSpace m → ℝ)) continuousOn_const hf
      (le_refl (0 : ℝ)) (fun _ _ => by simp [show m ≠ 0 by omega])
    simpa [thinFunctionalAt, determinantEnergyAt] using h
  · exact thinValueRealAt_nonneg hm hR o continuousOn_const

theorem determinantEnergyAt_smul {m : ℕ} (R : ℝ) (o : ThinSpace m)
    (c : ℝ) (f : ThinSpace m → ℝ) :
    determinantEnergyAt R o (c • f) = c^(m+1) * determinantEnergyAt R o f := by
  unfold determinantEnergyAt
  simp_rw [thinQuaternionHessian_smul, mooreDet_smul, Pi.smul_apply, smul_eq_mul]
  have he (z : ThinSpace m) : -(c*f z)*(c^m*mooreDet m (thinQuaternionHessian f z)) =
      c^(m+1)*((-f z)*mooreDet m (thinQuaternionHessian f z)) := by rw [pow_succ]; ring
  simp_rw [he]
  exact integral_const_mul _ _

theorem thinFunctionalAt_scaled_source {m : ℕ} (R : ℝ) (o : ThinSpace m)
    (c : ℝ) (ρ f : ThinSpace m → ℝ) :
    thinFunctionalAt R o (c^m • ρ) (c • f) = c^(m+1) * thinFunctionalAt R o ρ f := by
  unfold thinFunctionalAt
  rw [determinantEnergyAt_smul]
  have he (z : ThinSpace m) : (-(c • f) z) * (c^m • ρ) z =
      c^(m+1) * ((-f z)*ρ z) := by simp only [Pi.smul_apply, smul_eq_mul, pow_succ]; ring
  simp_rw [he, integral_const_mul]
  ring

theorem thinValueRealAt_pow_smul {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) {c : ℝ} (hc : 0 ≤ c) :
    thinValueRealAt R o (c^m • ρ) = c^(m+1) * thinValueRealAt R o ρ := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [show m ≠ 0 by omega, thinValueRealAt_zero hm hR o]
  have hcp : 0 < c^(m+1) := pow_pos hc _
  have hs : ContinuousOn (c^m • ρ) (thinClosedBallAt R o) := continuousOn_const.smul hρ
  apply le_antisymm
  · apply thinValueRealAt_le hm hR o hs
    intro f hf
    have hg := hf.smul (inv_pos.mpr hc).le
    have he : c • (c⁻¹ • f) = f := by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    calc
      thinFunctionalAt R o (c^m • ρ) f =
          c^(m+1) * thinFunctionalAt R o ρ (c⁻¹ • f) := by
        rw [← thinFunctionalAt_scaled_source, he]
      _ ≤ c^(m+1) * thinValueRealAt R o ρ :=
        mul_le_mul_of_nonneg_left (hg.functional_le_value hm hR hρ) hcp.le
  · have hb : thinValueRealAt R o ρ ≤ thinValueRealAt R o (c^m • ρ) / c^(m+1) := by
      apply thinValueRealAt_le hm hR o hρ
      intro f hf
      apply (le_div_iff₀ hcp).mpr
      have h := (hf.smul hc.le).functional_le_value hm hR hs
      rw [thinFunctionalAt_scaled_source] at h
      simpa only [mul_comm] using h
    nlinarith [(le_div_iff₀ hcp).mp hb]

theorem thinValueRealAt_smul {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) {a : ℝ} (ha : 0 ≤ a) :
    thinValueRealAt R o (a • ρ) = a^(((m : ℝ)+1)/m) * thinValueRealAt R o ρ := by
  let c := a^((m : ℝ)⁻¹)
  have hc : 0 ≤ c := Real.rpow_nonneg ha _
  have hcm : c^m = a := Real.rpow_inv_natCast_pow ha (by omega)
  have hcp : c^(m+1) = a^(((m : ℝ)+1)/m) := by
    rw [show c = a^((m : ℝ)⁻¹) from rfl, ← Real.rpow_mul_natCast ha]
    congr 1
    push_cast
    ring
  simpa only [hcm, hcp] using thinValueRealAt_pow_smul hm hR o hρ hc

theorem thinValueRealAt_convex {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {ρ σ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hσ : ContinuousOn σ (thinClosedBallAt R o)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    thinValueRealAt R o ((1-t)•ρ+t•σ) ≤
      (1-t)*thinValueRealAt R o ρ + t*thinValueRealAt R o σ := by
  have hs : ContinuousOn ((1-t)•ρ+t•σ) (thinClosedBallAt R o) :=
    (continuousOn_const.smul hρ).add (continuousOn_const.smul hσ)
  apply thinValueRealAt_le hm hR o hs
  intro f hf
  have he : thinFunctionalAt R o ((1-t)•ρ+t•σ) f =
      (1-t)*thinFunctionalAt R o ρ f + t*thinFunctionalAt R o σ f := by
    unfold thinFunctionalAt
    have hi (z : ThinSpace m) : (-f z)*(((1-t)•ρ+t•σ) z) =
        (1-t)*((-f z)*ρ z)+t*((-f z)*σ z) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    simp_rw [hi]
    rw [integral_add ((hf.source_integrableOn hR hρ).const_mul (1-t))
      ((hf.source_integrableOn hR hσ).const_mul t), integral_const_mul, integral_const_mul]
    ring
  rw [he]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hf.functional_le_value hm hR hρ) (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left (hf.functional_le_value hm hR hσ) ht.1)

theorem thinValueRealAt_relative_stability {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ σ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hσ : ContinuousOn σ (thinClosedBallAt R o)) {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1)
    (hcomp : ∀ z ∈ thinBallAt R o, (1-ε)*ρ z ≤ σ z ∧ σ z ≤ (1+ε)*ρ z) :
    (1-ε)^(((m : ℝ)+1)/m) * thinValueRealAt R o ρ ≤ thinValueRealAt R o σ ∧
      thinValueRealAt R o σ ≤ (1+ε)^(((m : ℝ)+1)/m) * thinValueRealAt R o ρ := by
  constructor
  · rw [← thinValueRealAt_smul hm hR o hρ (sub_nonneg.mpr hε.2)]
    exact thinValueRealAt_mono hm hR o (continuousOn_const.smul hρ) hσ
      (fun z hz => (hcomp z hz).1)
  · rw [← thinValueRealAt_smul hm hR o hρ (add_nonneg zero_le_one hε.1)]
    exact thinValueRealAt_mono hm hR o hσ (continuousOn_const.smul hρ)
      (fun z hz => (hcomp z hz).2)

theorem thinSource_realValue_lower_scaled {m : ℕ} (hm : 1 ≤ m) {R ε a : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (hεR : ε ≤ R/10) (ha : 0 ≤ a)
    (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hρ0 : ∀ z ∈ thinBallAt R o, 0 ≤ ρ z)
    (hρa : ∀ z ∈ thinCoreAt R ε o, a ≤ ρ z) :
    thinLowerConstant m * R^m * ε^(2*m+2) * a^(((m : ℝ)+1)/m) * Real.log (R/ε) ≤
      thinValueRealAt R o ρ := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_thinValueRealAt (show 1 ≤ m by omega) hR o hρ]
  exact thinSource_value_lower_scaled hm hR hε hεR ha o hρ hρ0 hρa

end KakeyaSharp
