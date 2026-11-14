/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.TubeGroups

@[expose] public section

/-! Restriction to a finite direction class and orthogonal invariance of
the actual weighted tube integral. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open Set Metric MeasureTheory Packet

theorem groupWeights_sum_reindex {N J K : ℕ} (owner : Fin N → Fin J)
    (weights : Fin N → ℝ) (j : Fin J) (e : Fin K ≃ {l : Fin N // owner l=j}) :
    (∑ l, groupWeights owner weights j l)=∑ k, weights (e k).val := by
  classical
  rw [e.sum_comp (fun l => weights l.val)]
  unfold groupWeights
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) weights

theorem groupWeights_power_reindex {N J K : ℕ} (owner : Fin N → Fin J)
    (weights : Fin N → ℝ) (j : Fin J) (e : Fin K ≃ {l : Fin N // owner l=j})
    {q : ℝ} (hq : q ≠ 0) :
    (∑ l, (groupWeights owner weights j l)^q)=∑ k, (weights (e k).val)^q := by
  have he (l : Fin N) : (groupWeights owner weights j l)^q=
      groupWeights owner (fun l => (weights l)^q) j l := by
    unfold groupWeights
    split_ifs <;> simp only [Real.zero_rpow hq]
  simp_rw [he]
  exact groupWeights_sum_reindex owner _ j e

theorem weightedTubeOverlap_group_reindex {n N J K : ℕ} (δ : ℝ)
    (owner : Fin N → Fin J) (v c : Fin N → Space n) (weights : Fin N → ℝ)
    (j : Fin J) (e : Fin K ≃ {l : Fin N // owner l=j}) (y : Space n) :
    weightedTubeOverlap δ v c (groupWeights owner weights j) y=
      weightedTubeOverlap δ (fun k => v (e k).val) (fun k => c (e k).val)
        (fun k => weights (e k).val) y := by
  have he (l : Fin N) :
      (tube (2*δ) (v l) (c l)).indicator (fun _ => groupWeights owner weights j l) y=
      groupWeights owner (fun l => (tube (2*δ) (v l) (c l)).indicator (fun _ => weights l) y) j l := by
    by_cases h : owner l=j <;> simp [groupWeights,h]
  unfold weightedTubeOverlap
  simp_rw [he]
  exact groupWeights_sum_reindex owner _ j e

theorem weightedTubeOverlap_rotation {n N : ℕ}
    (R : Space n ≃ₗᵢ[ℝ] Space n) (δ : ℝ)
    (v c : Fin N → Space n) (weights : Fin N → ℝ) (y : Space n) :
    weightedTubeOverlap δ (fun l => R (v l)) (fun l => R (c l)) weights (R y)=
      weightedTubeOverlap δ v c weights y := by
  apply Finset.sum_congr rfl
  intro l _
  have hm : R y ∈ tube (2*δ) (R (v l)) (R (c l)) ↔ y ∈ tube (2*δ) (v l) (c l) := by
    change y ∈ R ⁻¹' tube (2*δ) (R (v l)) (R (c l)) ↔ _
    rw [rotated_tube_preimage]
  by_cases hy : y ∈ tube (2*δ) (v l) (c l)
  · rw [Set.indicator_of_mem hy,Set.indicator_of_mem (hm.mpr hy)]
  · rw [Set.indicator_of_notMem hy,Set.indicator_of_notMem (mt hm.mp hy)]

theorem weightedTubeMoment_rotation {n N : ℕ}
    (R : Space n ≃ₗᵢ[ℝ] Space n) (δ q : ℝ)
    (v c : Fin N → Space n) (weights : Fin N → ℝ) :
    (∫ y, (weightedTubeOverlap δ v c weights y)^q)=
      ∫ y, (weightedTubeOverlap δ (fun l => R (v l)) (fun l => R (c l)) weights y)^q := by
  have h := integral_rotation R
    (fun y => (weightedTubeOverlap δ (fun l => R (v l)) (fun l => R (c l)) weights y)^q)
  simpa only [weightedTubeOverlap_rotation] using h

end KakeyaSharp.Graph
