/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Dirichlet.Descent
public import KakeyaSharp.ThinValueDerivative

@[expose] public section

/-! Actual admissible solutions and attainment of the variational value.
The existence theorem is deduced from the checked periodic Dirichlet solver.
No solution or analytic existence principle is supplied as a hypothesis. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp.Dirichlet
open Set MeasureTheory KakeyaSharp.Moore
open scoped ContDiff ComplexOrder

/-- A classical solution on the actual translated three-coordinate ball. -/
structure ThinDirichletSolution {m : ℕ} (R : ℝ) (o : ThinSpace m)
    (ρ : ThinSpace m → ℝ) where
  u : ThinSpace m → ℝ
  regularity : ContDiff ℝ 4 u
  admissible : ThinAdmissibleAt R o u
  positive : ∀ z ∈ thinClosedBallAt R o, ∀ w ≠ 0,
    0 < quaternionForm (thinQuaternionHessian u z) w
  equation : ∀ z ∈ thinClosedBallAt R o,
    mooreDet m (thinQuaternionHessian u z) = ρ z

/-- Positive smooth densities have genuine admissible solutions in every
positive quaternionic dimension, with arbitrary center and radius. -/
theorem exists_thinDirichletSolution {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ z ∈ thinClosedBallAt R o, 0 < ρ z) :
    Nonempty (ThinDirichletSolution R o ρ) := by
  cases m with
  | zero => omega
  | succ m =>
    let σ : ThinSpace (m+1) → ℝ := fun z => ρ (o+z)
    have hσ : ContDiff ℝ ∞ σ := hρ.comp (contDiff_const.add contDiff_id)
    have hσpos : ∀ z ∈ thinClosedBallAt R 0, 0 < σ z := by
      intro z hz
      apply hρpos
      simpa [thinClosedBallAt] using hz
    obtain ⟨v,hv,hvb,hvp,hve⟩ := exists_thin_ball_C4 m hR hσ hσpos
    let u : ThinSpace (m+1) → ℝ := fun z => v (z-o)
    have hu : ContDiff ℝ 4 u := hv.comp (contDiff_id.sub contDiff_const)
    have hmem (z : ThinSpace (m+1)) (hz : z ∈ thinClosedBallAt R o) :
        z-o ∈ thinClosedBallAt R 0 := by
      simpa [thinClosedBallAt] using hz
    have hH (z : ThinSpace (m+1)) :
        thinQuaternionHessian u z = thinQuaternionHessian v (z-o) :=
      thinQuaternionHessian_comp_sub o v z
    have hpos (z : ThinSpace (m+1)) (hz : z ∈ thinClosedBallAt R o) :
        (complexify (thinQuaternionHessian u z)).PosDef := by
      rw [hH]
      exact hvp _ (hmem z hz)
    have hherm (z : ThinSpace (m+1)) :=
      thinQuaternionHessian_isHermitian ((hu.of_le (by norm_num)).contDiffAt (x := z))
    refine ⟨⟨u,hu,⟨?_,?_,?_⟩,?_,?_⟩⟩
    · intro z _
      exact (hu.of_le (by norm_num)).contDiffAt
    · intro z hz
      exact hvb (z-o) (by simpa using hz)
    · intro z hz
      exact (complexify_posSemidef_iff (hherm z)).mp (hpos z hz).posSemidef
    · intro z hz
      exact (complexify_posDef_iff (hherm z)).mp (hpos z hz)
    · intro z hz
      rw [hH, hve _ (hmem z hz)]
      simp [σ]

theorem ThinDirichletSolution.maximizes {m : ℕ} {R : ℝ} (hR : 0 < R)
    {o : ThinSpace m} {ρ : ThinSpace m → ℝ}
    (S : ThinDirichletSolution R o ρ)
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    {v : ThinSpace m → ℝ} (hv : ThinAdmissibleAt R o v) :
    thinFunctionalAt R o ρ v ≤ thinFunctionalAt R o ρ S.u :=
  S.admissible.maximizes_of_detEquation hR hρ hv
    (fun z hz => S.equation z (show z ∈ thinClosedBallAt R o from
      (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 < R^2 from hz).le))

theorem ThinDirichletSolution.value_eq {m : ℕ} {R : ℝ} (hR : 0 < R)
    {o : ThinSpace m} {ρ : ThinSpace m → ℝ}
    (S : ThinDirichletSolution R o ρ)
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) :
    thinValueRealAt R o ρ =
      (m : ℝ)/((m : ℝ)+1) * ∫ z in thinBallAt R o, (-S.u z)*ρ z :=
  thinValueRealAt_PDE_representation hR hρ S.admissible
    (fun z hz => S.equation z (show z ∈ thinClosedBallAt R o from
      (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 < R^2 from hz).le))

/-- The supremum is attained for every smooth positive source. -/
theorem exists_thinVariational_maximizer {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ z ∈ thinClosedBallAt R o, 0 < ρ z) :
    ∃ u : ThinSpace m → ℝ, ThinAdmissibleAt R o u ∧
      thinVariationalValueAt R o ρ = (thinFunctionalAt R o ρ u : EReal) ∧
      thinValueRealAt R o ρ =
        (m : ℝ)/((m : ℝ)+1) * ∫ z in thinBallAt R o, (-u z)*ρ z := by
  obtain ⟨S⟩ := exists_thinDirichletSolution hm hR o hρ hρpos
  exact ⟨S.u,S.admissible,
    thinVariationalValueAt_eq_of_detEquation hR hρ.continuous.continuousOn
      S.admissible (fun z hz => S.equation z (show z ∈ thinClosedBallAt R o from
      (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 < R^2 from hz).le)),
    S.value_eq hR hρ.continuous.continuousOn⟩

end KakeyaSharp.Dirichlet
