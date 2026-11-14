/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.SpatialLocalization

@[expose] public section

/-! The graph-tube bound with arbitrary intercepts. The constant depends
only on dimension; no bounded-location hypothesis remains. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

theorem exists_globalGraphTube_constant {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      ∀ (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, (∑ j, (v l j)^2) ≤ 1/16) →
      (∀ i j, i ≠ j → δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) →
      normalizedTubeMoment (128*δ) a v weights ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_enlargedGraphTube_constant hm (by norm_num : (0 : ℝ) ≤ 4)
  refine ⟨spatialGroupFactor m*C,mul_pos (spatialGroupFactor_pos m) hC,?_⟩
  intro N δ hδ hδ1 a v weights hw hv hsep
  obtain ⟨J,b,_,hbsep,hcover⟩ := compact_finite_separated_net
    (Set.finite_range (fun l => (WithLp.toLp 2 (a l) : Space m))).isCompact
    (by norm_num : (0 : ℝ) < 2)
  have hc (l : Fin N) : ∃ j, dist (WithLp.toLp 2 (a l) : Space m) (b j) ≤ 2 :=
    hcover _ ⟨l,rfl⟩
  choose owner howner using hc
  have h := normalizedTubeMoment_spatial_le (by omega : 1 ≤ m) hδ hδ1.le
    owner a v hw b howner (fun i j hij => (hbsep i j hij).le) hv
  have hlocal (j : Fin J) :
      normalizedTubeMoment (128*δ) a v (groupWeights owner weights j) ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (groupWeights owner weights j l)^(inputExponent m)) := by
    rw [normalizedTubeMoment_group_translate (128*δ) owner a v weights b j]
    exact hbound N δ hδ hδ1 (relativeIntercept owner a b j) v (groupWeights owner weights j)
      (groupWeights_nonneg owner hw j) (relativeIntercept_bound owner a b howner j) hv hsep
  calc
    _ ≤ spatialGroupFactor m*(∑ j, normalizedTubeMoment (128*δ) a v (groupWeights owner weights j)) := h
    _ ≤ spatialGroupFactor m*(∑ j, C*Real.log (2/δ)*δ^m*
        (∑ l, (groupWeights owner weights j l)^(inputExponent m))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hlocal j)) (spatialGroupFactor_pos m).le
    _ = _ := by
      rw [← Finset.mul_sum,groupWeights_power_sum owner weights
        (by have hq := inputExponent_ge_one (m := m) (by omega); linarith)]
      ring

end KakeyaSharp.Packet
