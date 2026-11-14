/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ChartTubes
public import KakeyaSharp.SharpTransfer

@[expose] public section

/-! Exact restriction and translation identities for weighted Euclidean tubes.
The integrability assertions use finite-volume tubes and require no overlap estimate. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open Set Metric MeasureTheory Packet

def relativeCenter {n N J : ℕ} (owner : Fin N → Fin J)
    (c : Fin N → Space n) (b : Fin J → Space n) (j : Fin J) (l : Fin N) : Space n :=
  if owner l=j then c l-b j else 0

theorem weightedTubeOverlap_power_integrable {n N : ℕ} (δ : ℝ)
    (v c : Fin N → Space n) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    {q : ℝ} (hq : 0 < q) :
    Integrable (fun y => (weightedTubeOverlap δ v c weights y)^q) := by
  have hLp : MemLp (weightedTubeOverlap δ v c weights) (ENNReal.ofReal q) volume :=
    memLp_weighted_tubes (2*δ) v c weights q
  have h := hLp.integrable_norm_rpow (by positivity : ENNReal.ofReal q ≠ 0) ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal hq.le,
    Real.norm_of_nonneg (weightedTubeOverlap_nonneg δ v c hw _)] using h

theorem mem_tube_translate {n : ℕ} (r : ℝ) (v c b y : Space n) :
    y-b ∈ tube r v (c-b) ↔ y ∈ tube r v c := by
  simp only [mem_tube_iff]
  apply exists_congr
  intro t
  rw [show c-b+t • v=(c+t • v)-b by abel,dist_sub_right]

theorem relativeCenter_norm_le {n N J : ℕ} (owner : Fin N → Fin J)
    (c : Fin N → Space n) (b : Fin J → Space n)
    (hnear : ∀ l, dist (c l) (b (owner l)) ≤ 2) (j : Fin J) (l : Fin N) :
    ‖relativeCenter owner c b j l‖ ≤ 2 := by
  by_cases h : owner l=j
  · simpa only [relativeCenter,h,ite_true,dist_eq_norm] using hnear l
  · simp [relativeCenter,h]

theorem weightedTubeOverlap_group_sum {n N J : ℕ} (δ : ℝ)
    (owner : Fin N → Fin J) (v c : Fin N → Space n) (weights : Fin N → ℝ)
    (y : Space n) :
    weightedTubeOverlap δ v c weights y=
      ∑ j, weightedTubeOverlap δ v c (groupWeights owner weights j) y := by
  unfold weightedTubeOverlap groupWeights
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : y ∈ tube (2*δ) (v l) (c l) <;> simp [h]

theorem weightedTubeOverlap_group_translate {n N J : ℕ} (δ : ℝ)
    (owner : Fin N → Fin J) (v c : Fin N → Space n) (weights : Fin N → ℝ)
    (b : Fin J → Space n) (j : Fin J) (y : Space n) :
    weightedTubeOverlap δ v c (groupWeights owner weights j) y=
      weightedTubeOverlap δ v (relativeCenter owner c b j)
        (groupWeights owner weights j) (y-b j) := by
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : owner l=j
  · simp only [relativeCenter,h,ite_true]
    by_cases hy : y ∈ tube (2*δ) (v l) (c l)
    · simp only [Set.indicator_of_mem hy,
        Set.indicator_of_mem ((mem_tube_translate _ _ _ _ _).mpr hy)]
    · simp only [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (mt (mem_tube_translate _ _ _ _ _).mp hy)]
  · simp [groupWeights,h]

theorem weightedTubeMoment_group_translate {n N J : ℕ} (δ q : ℝ)
    (owner : Fin N → Fin J) (v c : Fin N → Space n) (weights : Fin N → ℝ)
    (b : Fin J → Space n) (j : Fin J) :
    (∫ y, (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^q)=
      ∫ y, (weightedTubeOverlap δ v (relativeCenter owner c b j)
        (groupWeights owner weights j) y)^q := by
  simp_rw [weightedTubeOverlap_group_translate δ owner v c weights b j]
  simpa only [sub_eq_neg_add] using integral_add_left_eq_self
    (μ := (volume : Measure (Space n)))
    (fun y => (weightedTubeOverlap δ v (relativeCenter owner c b j)
      (groupWeights owner weights j) y)^q) (-b j)

theorem weightedTubeOverlap_group_near {n N J : ℕ} {δ : ℝ} (hδ1 : δ ≤ 1)
    (owner : Fin N → Fin J) (v c : Fin N → Space n) (weights : Fin N → ℝ)
    (b : Fin J → Space n) (hnear : ∀ l, dist (c l) (b (owner l)) ≤ 2)
    (hv : ∀ l, ‖v l‖=1) (j : Fin J) {y : Space n}
    (hy : weightedTubeOverlap δ v c (groupWeights owner weights j) y ≠ 0) :
    dist (b j) y ≤ 6 := by
  obtain ⟨l,_,hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  have hmem : y ∈ tube (2*δ) (v l) (c l) := by
    by_contra hn
    simp only [Set.indicator_of_notMem hn,ne_eq,not_true_eq_false] at hl
  have ho : owner l=j := by
    by_contra hn
    simp [groupWeights,hn] at hl
  have hc := hnear l
  rw [ho] at hc
  have hd := tube_subset_ball (2*δ) (v l) (c l) hmem
  simp only [mem_ball,hv l] at hd
  have ht := dist_triangle (b j) (c l) y
  rw [dist_comm (b j) (c l),dist_comm (c l) y] at ht
  linarith

end KakeyaSharp.Graph
