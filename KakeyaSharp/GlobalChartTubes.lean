/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.TubeSpatialLocalization

@[expose] public section

/-! The sharp Euclidean tube estimate in a fixed direction chart,
with no restriction on any spatial center. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open Set Metric MeasureTheory Packet

theorem exists_globalChartTube_constant {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v c : Fin N → Space (m+1)) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, ‖v l‖=1) →
      (∀ l, dist (v l) (north m) ≤ 1/16) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      (∫ y, (weightedTubeOverlap δ v c weights y)^(inputExponent m)) ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_chartTube_constant hm
  refine ⟨tubeGroupFactor (m+1) (inputExponent m)*C,
    mul_pos (tubeGroupFactor_pos _ _) hC,?_⟩
  intro N δ hδ hδ1 v c weights hw hv hcap hsep
  obtain ⟨J,b,_,hbsep,hcover⟩ := compact_finite_separated_net
    (Set.finite_range c).isCompact (by norm_num : (0 : ℝ) < 2)
  have hc (l : Fin N) : ∃ j, dist (c l) (b j) ≤ 2 := hcover _ ⟨l,rfl⟩
  choose owner howner using hc
  have hq := inputExponent_ge_one (m := m) (by omega)
  have h := weightedTubeMoment_spatial_le hq hδ1 owner v c hw b howner
    (fun i j hij => (hbsep i j hij).le) hv
  have hlocal (j : Fin J) :
      (∫ y, (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^(inputExponent m)) ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (groupWeights owner weights j l)^(inputExponent m)) := by
    rw [weightedTubeMoment_group_translate δ (inputExponent m) owner v c weights b j]
    apply hbound N δ hδ hδ1 v (relativeCenter owner c b j)
      (groupWeights owner weights j) (groupWeights_nonneg owner hw j) hv hcap _ hsep
    intro l
    exact abs_le.mp ((abs_head_le_norm _).trans (relativeCenter_norm_le owner c b howner j l))
  calc
    _ ≤ tubeGroupFactor (m+1) (inputExponent m)*
        (∑ j, ∫ y, (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^(inputExponent m)) := h
    _ ≤ tubeGroupFactor (m+1) (inputExponent m)*(∑ j,
        C*Real.log (2/δ)*δ^m*(∑ l, (groupWeights owner weights j l)^(inputExponent m))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hlocal j)) (tubeGroupFactor_pos _ _).le
    _ = _ := by
      rw [← Finset.mul_sum,groupWeights_power_sum owner weights (by linarith : inputExponent m ≠ 0)]
      ring

end KakeyaSharp.Graph
