/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Dirichlet.Comparison
public import KakeyaSharp.VariationalContinuity

@[expose] public section

/-! Finite-ball localization for the actual variational value. Positivity
is removed by the proved source-continuity theorem. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp
open Set MeasureTheory Filter Dirichlet
open scoped ContDiff Topology

theorem thinValueRealAt_localization_positive {m N : ℕ} (hm : 1 ≤ m)
    {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    (r : Fin N → ℝ) (c : Fin N → ThinSpace m) (hr : ∀ j, 0 < r j)
    (hsub : ∀ j, thinClosedBallAt (r j) (c j) ⊆ thinBallAt R o)
    (hdis : Pairwise (fun i j => Disjoint (thinBallAt (r i) (c i)) (thinBallAt (r j) (c j))))
    {ρ : ThinSpace m → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hp : ∀ z ∈ thinClosedBallAt R o, 0 < ρ z) :
    (∑ j, thinValueRealAt (r j) (c j) ρ) ≤ thinValueRealAt R o ρ := by
  classical
  have hclosed : thinBallAt R o ⊆ thinClosedBallAt R o :=
    fun z hz => (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 < R^2 from hz).le
  have hsmall (j : Fin N) : thinBallAt (r j) (c j) ⊆ thinClosedBallAt (r j) (c j) :=
    fun z hz => (show ‖z.1-(c j).1‖^2+‖z.2-(c j).2‖^2 < (r j)^2 from hz).le
  obtain ⟨S⟩ := exists_thinDirichletSolution hm hR o hρ hp
  have hex (j : Fin N) : Nonempty (ThinDirichletSolution (r j) (c j) ρ) :=
    exists_thinDirichletSolution hm (hr j) (c j) hρ
      (fun z hz => hp z (hclosed (hsub j hz)))
  let T : ∀ j, ThinDirichletSolution (r j) (c j) ρ := fun j => Classical.choice (hex j)
  have hcmp (j : Fin N) := S.le_on_subball hm hR (hr j) (T j) ((hsub j).trans hclosed)
  have hgi := S.admissible.source_integrableOn hR hρ.continuous.continuousOn
  have hli (j : Fin N) := (T j).admissible.source_integrableOn (hr j) hρ.continuous.continuousOn
  have hgi' (j : Fin N) := hgi.mono_set ((hsmall j).trans (hsub j))
  have hsum : (∑ j, ∫ z in thinBallAt (r j) (c j), (-(T j).u z)*ρ z) ≤
      ∑ j, ∫ z in thinBallAt (r j) (c j), (-S.u z)*ρ z := by
    apply Finset.sum_le_sum
    intro j _
    apply setIntegral_mono_on (hli j) (hgi' j) (thinBallAt_isOpen _ _).measurableSet
    intro z hz
    exact mul_le_mul_of_nonneg_right (neg_le_neg (hcmp j z (hsmall j hz)))
      (hp z (hclosed (hsub j (hsmall j hz)))).le
  have hunion : (⋃ j, thinBallAt (r j) (c j)) ⊆ thinBallAt R o :=
    iUnion_subset (fun j => (hsmall j).trans (hsub j))
  have htotal : (∑ j, ∫ z in thinBallAt (r j) (c j), (-S.u z)*ρ z) ≤
      ∫ z in thinBallAt R o, (-S.u z)*ρ z := by
    rw [← integral_iUnion_fintype (fun j => (thinBallAt_isOpen _ _).measurableSet) hdis hgi']
    apply setIntegral_mono_set hgi
      ((ae_restrict_iff' (thinBallAt_isOpen R o).measurableSet).mpr (ae_of_all _ (fun z hz =>
        mul_nonneg (neg_nonneg.mpr (S.admissible.nonpos hm hR z (hclosed hz)))
          (hp z (hclosed hz)).le)))
    exact Filter.Eventually.of_forall (fun _ hx => hunion hx)
  rw [S.value_eq hR hρ.continuous.continuousOn]
  have he (j : Fin N) := (T j).value_eq (hr j) hρ.continuous.continuousOn
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hsum.trans htotal) (by positivity)

/-- Localization allows zero densities and arbitrary nonnegative smooth sources.
The closed smaller balls lie inside the outer open ball; their open interiors
are pairwise disjoint. No solution or comparison hypothesis is supplied. -/
theorem thinValueRealAt_localization {m N : ℕ} (hm : 1 ≤ m)
    {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    (r : Fin N → ℝ) (c : Fin N → ThinSpace m) (hr : ∀ j, 0 < r j)
    (hsub : ∀ j, thinClosedBallAt (r j) (c j) ⊆ thinBallAt R o)
    (hdis : Pairwise (fun i j => Disjoint (thinBallAt (r i) (c i)) (thinBallAt (r j) (c j))))
    {ρ : ThinSpace m → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hp : ∀ z ∈ thinClosedBallAt R o, 0 ≤ ρ z) :
    (∑ j, thinValueRealAt (r j) (c j) ρ) ≤ thinValueRealAt R o ρ := by
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hε0 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 ≤ ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hpos
    exact hpos.le
  have hleft := tendsto_finsetSum Finset.univ (fun j _ =>
    thinValueRealAt_regularization hm (hr j) (c j) hρ.continuous.continuousOn hε hε0)
  have hright := thinValueRealAt_regularization hm hR o hρ.continuous.continuousOn hε hε0
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with ε hpos
  exact thinValueRealAt_localization_positive hm hR o r c hr hsub hdis
    (hρ.add contDiff_const) (fun z hz => add_pos_of_nonneg_of_pos (hp z hz) hpos)

/-- The logarithmic thin-source test can be summed over disjoint balls. -/
theorem thinValueRealAt_localized_thin_lower {m N : ℕ} (hm : 1 ≤ m)
    {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    (r ε a : Fin N → ℝ) (c : Fin N → ThinSpace m)
    (hr : ∀ j, 0 < r j) (hε : ∀ j, 0 < ε j) (hεr : ∀ j, ε j ≤ r j/10)
    (ha : ∀ j, 0 ≤ a j)
    (hsub : ∀ j, thinClosedBallAt (r j) (c j) ⊆ thinBallAt R o)
    (hdis : Pairwise (fun i j => Disjoint (thinBallAt (r i) (c i)) (thinBallAt (r j) (c j))))
    {ρ : ThinSpace m → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hp : ∀ z ∈ thinClosedBallAt R o, 0 ≤ ρ z)
    (hlower : ∀ j z, z ∈ thinCoreAt (r j) (ε j) (c j) → a j ≤ ρ z) :
    (∑ j, thinLowerConstant m*(r j)^m*(ε j)^(2*m+2)*
      (a j)^(((m : ℝ)+1)/m)*Real.log (r j/ε j)) ≤ thinValueRealAt R o ρ := by
  apply le_trans _ (thinValueRealAt_localization (by omega) hR o r c hr hsub hdis hρ hp)
  apply Finset.sum_le_sum
  intro j _
  apply thinSource_realValue_lower_scaled hm (hr j) (hε j) (hεr j) (ha j) (c j)
    hρ.continuous.continuousOn _ (hlower j)
  intro z hz
  have hz' : z ∈ thinClosedBallAt (r j) (c j) :=
    (show ‖z.1-(c j).1‖^2+‖z.2-(c j).2‖^2 < (r j)^2 from hz).le
  exact hp z (show z ∈ thinClosedBallAt R o from
    (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 < R^2 from hsub j hz').le)

end KakeyaSharp
