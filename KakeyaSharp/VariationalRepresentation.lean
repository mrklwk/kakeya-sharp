/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.LocalExtension
public import KakeyaSharp.VariationalValue

@[expose] public section

/-! The supporting inequality and PDE representation for the original admissible class.
A solution is an explicit hypothesis; no nonlinear existence theorem is assumed. -/
noncomputable section
namespace KakeyaSharp
open Set Filter MeasureTheory KakeyaSharp.Moore
open scoped Topology ContDiff

theorem ThinAdmissibleAt.exists_C3_representative {m : ℕ} {R : ℝ} (hR : 0 < R)
    {o : ThinSpace m} {f : ThinSpace m → ℝ} (hf : ThinAdmissibleAt R o f) :
    ∃ g : ThinSpace m → ℝ, ContDiff ℝ 3 g ∧
      (∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → g z = 0) ∧
      (∀ z ∈ thinBallAt R o, ∀ w, 0 ≤ quaternionForm (thinQuaternionHessian g z) w) ∧
      (∀ z ∈ thinClosedBallAt R o, g =ᶠ[𝓝 z] f) := by
  obtain ⟨g,hg,hgf⟩ := exists_global_C3_extension (thinClosedBallAt_compact hR.le o)
    hf.1
  refine ⟨g,hg,?_,?_,hgf⟩
  · intro z hz
    rw [(hgf z (show z ∈ thinClosedBallAt R o from hz.le)).self_of_nhds]
    exact hf.2.1 z hz
  · intro z hz w
    have hz' : z ∈ thinClosedBallAt R o :=
      show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le
    rw [thinQuaternionHessian_congr_nhds (hgf z hz')]
    exact hf.2.2 z hz' w

theorem ThinAdmissibleAt.supporting_inequality {m : ℕ} {R : ℝ}
    (hR : 0 < R) {o : ThinSpace m} {ρ u v : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hu : ThinAdmissibleAt R o u) (hv : ThinAdmissibleAt R o v) :
    thinFunctionalAt R o ρ v - thinFunctionalAt R o ρ u ≤
      ∫ z in thinBallAt R o, (v z-u z)*(mooreDet m (thinQuaternionHessian u z)-ρ z) := by
  obtain ⟨u',hu',hzu',hpu',heu⟩ := hu.exists_C3_representative hR
  obtain ⟨v',hv',hzv',hpv',hev⟩ := hv.exists_C3_representative hR
  have h := thinFunctional_supporting_inequality hR o hρ hu' hv' hzu' hzv' hpu' hpv'
  rw [thinFunctionalAt_congr_nhds R o ρ heu, thinFunctionalAt_congr_nhds R o ρ hev] at h
  have he : (∫ z in thinBallAt R o, (v' z-u' z)*(mooreDet m (thinQuaternionHessian u' z)-ρ z)) =
      ∫ z in thinBallAt R o, (v z-u z)*(mooreDet m (thinQuaternionHessian u z)-ρ z) := by
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    have hz' : z ∈ thinClosedBallAt R o :=
      show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le
    dsimp only
    rw [(heu z hz').self_of_nhds, (hev z hz').self_of_nhds,
      thinQuaternionHessian_congr_nhds (heu z hz')]
  rwa [he] at h

theorem ThinAdmissibleAt.maximizes_of_detEquation {m : ℕ} {R : ℝ}
    (hR : 0 < R) {o : ThinSpace m} {ρ u v : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hu : ThinAdmissibleAt R o u) (hv : ThinAdmissibleAt R o v)
    (hEq : ∀ z ∈ thinBallAt R o, mooreDet m (thinQuaternionHessian u z) = ρ z) :
    thinFunctionalAt R o ρ v ≤ thinFunctionalAt R o ρ u := by
  have h := hu.supporting_inequality hR hρ hv
  have hz : (∫ z in thinBallAt R o, (v z-u z)*(mooreDet m (thinQuaternionHessian u z)-ρ z)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro z hz
    rw [hEq z hz, sub_self, mul_zero]
  rw [hz] at h
  exact sub_nonpos.mp h

theorem thinVariationalValueAt_eq_of_detEquation {m : ℕ} {R : ℝ}
    (hR : 0 < R) {o : ThinSpace m} {ρ u : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) (hu : ThinAdmissibleAt R o u)
    (hEq : ∀ z ∈ thinBallAt R o, mooreDet m (thinQuaternionHessian u z) = ρ z) :
    thinVariationalValueAt R o ρ = (thinFunctionalAt R o ρ u : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro v
    exact EReal.coe_le_coe_iff.mpr (hu.maximizes_of_detEquation hR hρ v.property hEq)
  · exact le_iSup (fun f : {f : ThinSpace m → ℝ // ThinAdmissibleAt R o f} =>
      (thinFunctionalAt R o ρ f : EReal)) ⟨u,hu⟩

theorem thinFunctionalAt_eq_of_detEquation {m : ℕ} (R : ℝ) (o : ThinSpace m)
    {ρ u : ThinSpace m → ℝ}
    (hEq : ∀ z ∈ thinBallAt R o, mooreDet m (thinQuaternionHessian u z) = ρ z) :
    thinFunctionalAt R o ρ u =
      (m : ℝ)/((m : ℝ)+1) * ∫ z in thinBallAt R o, (-u z)*ρ z := by
  have he : determinantEnergyAt R o u = ∫ z in thinBallAt R o, (-u z)*ρ z := by
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only
    rw [hEq z hz]
  unfold thinFunctionalAt
  rw [he]
  have hm : (m : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem thinVariationalValueAt_PDE_representation {m : ℕ} {R : ℝ}
    (hR : 0 < R) {o : ThinSpace m} {ρ u : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) (hu : ThinAdmissibleAt R o u)
    (hEq : ∀ z ∈ thinBallAt R o, mooreDet m (thinQuaternionHessian u z) = ρ z) :
    thinVariationalValueAt R o ρ =
      (((m : ℝ)/((m : ℝ)+1) * ∫ z in thinBallAt R o, (-u z)*ρ z : ℝ) : EReal) := by
  rw [thinVariationalValueAt_eq_of_detEquation hR hρ hu hEq,
    thinFunctionalAt_eq_of_detEquation R o hEq]

end KakeyaSharp

