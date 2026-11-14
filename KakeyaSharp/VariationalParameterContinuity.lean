/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.VariationalContinuity
public import KakeyaSharp.ThinParameterHessian

@[expose] public section

/-! Joint source continuity implies continuity of the variational value in
the parameter, including where the source vanishes. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace KakeyaSharp
open Set Filter
open scoped Topology

theorem thinValueRealAt_continuousOn_parameter {m : ℕ} (hm : 1 ≤ m)
    {R : ℝ} (hR : 0 < R) (o : ThinSpace m) {Ω : Set (Space 3)} (hΩ : IsOpen Ω)
    {ρ : ThinCurrentSpace m → ℝ} (hρ : ContinuousOn ρ (Ω ×ˢ thinClosedBallAt R o)) :
    ContinuousOn (fun p => thinValueRealAt R o (thinSlice ρ p)) Ω := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  obtain ⟨K,hK,hpK,hKΩ⟩ := exists_compact_subset hΩ hp
  have hKnhds : K ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp hpK
  have hpK' : p ∈ K := interior_subset hpK
  have hB := thinClosedBallAt_compact hR.le o
  have hc : ContinuousOn ρ (K ×ˢ thinClosedBallAt R o) :=
    hρ.mono (fun _ hy => ⟨hKΩ hy.1,hy.2⟩)
  have hs (q : Space 3) (hq : q ∈ K) :
      ContinuousOn (thinSlice ρ q) (thinClosedBallAt R o) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun z hz => ⟨hq,hz⟩)
  have hu : TendstoUniformlyOn (fun q z => ρ (q,z)) (fun z => ρ (p,z))
      (𝓝 p) (thinClosedBallAt R o) := by
    have hu := ((hK.prod hB).uniformContinuousOn_of_continuous hc).tendstoUniformlyOn
      (F := fun q z => ρ (q,z)) hpK'
    rwa [nhdsWithin_eq_nhds.mpr hKnhds] at hu
  obtain ⟨C,hC⟩ := (hK.prod hB).exists_bound_of_continuousOn hc
  let A : ℝ := max C 0
  have hA : 0 ≤ A := le_max_right _ _
  have hb (q : Space 3) (hq : q ∈ K) (z : ThinSpace m) (hz : z ∈ thinBallAt R o) :
      thinSlice ρ q z ≤ A :=
    (le_abs_self _).trans ((hC (q,z) ⟨hq,show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le⟩).trans
      (le_max_left _ _))
  let L : ℝ := (A+1)^(((m : ℝ)+1)/m)*thinValueRealAt R o (fun _ => 1)
  have hL : 0 ≤ L := mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (thinValueRealAt_nonneg hm hR o continuousOn_const)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let a : ℝ := min 1 (ε/(L+1))
  have ha : 0 < a := lt_min (by norm_num) (div_pos hε (by linarith))
  have ha1 : a ≤ 1 := min_le_left _ _
  have haε : a*(L+1) ≤ ε := (le_div_iff₀ (by linarith : 0 < L+1)).mp (min_le_right _ _)
  have he := Metric.tendstoUniformlyOn_iff.mp hu a ha
  filter_upwards [hKnhds,he] with q hq hclose
  rw [Real.dist_eq]
  have hv := thinValueRealAt_lipschitz_bound hm hR o (hs q hq) (hs p hpK') hA ⟨ha.le,ha1⟩
    (hb q hq) (hb p hpK') (fun z hz => by
      have hc' := hclose z (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)
      simpa only [Real.dist_eq, thinSlice, abs_sub_comm] using hc'.le)
  exact hv.trans_lt (by dsimp only [L] at *; nlinarith)

end KakeyaSharp
