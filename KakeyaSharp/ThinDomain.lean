/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.AdmissibleIntegrability

@[expose] public section

/-! Geometric boundary properties of the actual Euclidean balls in the product space. -/
noncomputable section
namespace KakeyaSharp
open Set MeasureTheory

theorem thinBallAt_isOpen {m : ℕ} (R : ℝ) (o : ThinSpace m) :
    IsOpen (thinBallAt R o) := isOpen_lt (by fun_prop) continuous_const

theorem thinBallAt_convex {m : ℕ} (R : ℝ) (o : ThinSpace m) :
    Convex ℝ (thinBallAt R o) := by
  have hx : ConvexOn ℝ univ (fun z : ThinSpace m => ‖z.1 - o.1‖ ^ 2) := by
    simpa [dist_eq_norm, Function.comp_def, Pi.pow_def] using
      (((convexOn_univ_dist o.1).pow (fun _ _ => dist_nonneg) 2).comp_linearMap
        (LinearMap.fst ℝ (Space m) (ThinTransverseSpace m)))
  have hp : ConvexOn ℝ univ (fun z : ThinSpace m => ‖z.2 - o.2‖ ^ 2) := by
    simpa [dist_eq_norm, Function.comp_def, Pi.pow_def] using
      (((convexOn_univ_dist o.2).pow (fun _ _ => dist_nonneg) 2).comp_linearMap
        (LinearMap.snd ℝ (Space m) (ThinTransverseSpace m)))
  simpa [thinBallAt] using (hx.add hp).convex_lt (R ^ 2)

theorem thinBallAt_bounded {m : ℕ} {R : ℝ} (hR : 0 ≤ R) (o : ThinSpace m) :
    Bornology.IsBounded (thinBallAt R o) :=
  (thinClosedBallAt_compact hR o).isBounded.subset
    (fun z hz => show ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 ≤ R ^ 2 from hz.le)

theorem thinBallAt_frontier_subset {m : ℕ} (R : ℝ) (o : ThinSpace m) :
    frontier (thinBallAt R o) ⊆
      {z | ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 = R ^ 2} := by
  have hc : IsClosed (thinClosedBallAt R o) := isClosed_le (by fun_prop) continuous_const
  have hs : closure (thinBallAt R o) ⊆ thinClosedBallAt R o :=
    closure_minimal
      (fun z hz => show ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 ≤ R ^ 2 from hz.le) hc
  intro z hz
  have hle := hs hz.1
  have hn : z ∉ thinBallAt R o := by
    simpa only [(thinBallAt_isOpen R o).interior_eq] using hz.2
  exact le_antisymm hle (not_lt.mp hn)

theorem thinBallAt_null_frontier {m : ℕ} (R : ℝ) (o : ThinSpace m) :
    (volume : Measure (ThinSpace m)) (frontier (thinBallAt R o)) = 0 := by
  let : (volume : Measure (ThinSpace m)).IsAddHaarMeasure := by
    change ((volume : Measure (Space m)).prod (volume : Measure (ThinTransverseSpace m))).IsAddHaarMeasure
    infer_instance
  exact (thinBallAt_convex R o).addHaar_frontier volume

end KakeyaSharp

