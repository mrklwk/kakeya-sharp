/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.TubeGroups

@[expose] public section

/-! Spatial partition of actual Euclidean tubes with a dimension-only
overlap factor, independent of the positions and number of occupied regions. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open Set Metric MeasureTheory Packet

def tubeGroupFactor (n : ℕ) (q : ℝ) : ℝ := ((8 : ℝ)^n)^(q-1)

theorem tubeGroupFactor_pos (n : ℕ) (q : ℝ) : 0 < tubeGroupFactor n q :=
  Real.rpow_pos_of_pos (by positivity) _

theorem weightedTubeOverlap_spatial_power_le {n N J : ℕ} {q : ℝ} (hq : 1 ≤ q)
    {δ : ℝ} (hδ1 : δ ≤ 1) (owner : Fin N → Fin J)
    (v c : Fin N → Space n) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (b : Fin J → Space n) (hnear : ∀ l, dist (c l) (b (owner l)) ≤ 2)
    (hsep : ∀ i j, i ≠ j → 2 ≤ dist (b i) (b j))
    (hv : ∀ l, ‖v l‖=1) (y : Space n) :
    (weightedTubeOverlap δ v c weights y)^q ≤ tubeGroupFactor n q*
      ∑ j, (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^q := by
  let s := Finset.univ.filter (fun j => dist (b j) y ≤ 6)
  let g : Fin J → ℝ := fun j => weightedTubeOverlap δ v c (groupWeights owner weights j) y
  have hg (j : Fin J) : 0 ≤ g j :=
    weightedTubeOverlap_nonneg δ v c (groupWeights_nonneg owner hw j) y
  have hcard : (s.card : ℝ) ≤ (8 : ℝ)^n := by
    simpa only [show (3 : ℝ)*2=6 by norm_num] using
      direction_cap_card_le (by norm_num : (0 : ℝ) < 2) b hsep y
  have he : ∑ j, g j = ∑ j ∈ s, g j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · rfl
    · by_contra hn
      exact hj (weightedTubeOverlap_group_near hδ1 owner v c weights b hnear hv j hn)
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s
    (f := g) hq (fun j _ => hg j)
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg s.card) hcard (sub_nonneg.mpr hq)
  have hsum : 0 ≤ ∑ j ∈ s, (g j)^q :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (hg j) _)
  calc
    _ = (∑ j, g j)^q := by rw [weightedTubeOverlap_group_sum δ owner]
    _ = (∑ j ∈ s, g j)^q := by rw [he]
    _ ≤ (s.card : ℝ)^(q-1)*(∑ j ∈ s, (g j)^q) := hh
    _ ≤ tubeGroupFactor n q*(∑ j ∈ s, (g j)^q) := mul_le_mul_of_nonneg_right hpow hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_univ_sum_of_nonneg (fun j => Real.rpow_nonneg (hg j) _))
      (tubeGroupFactor_pos n q).le

theorem weightedTubeMoment_spatial_le {n N J : ℕ} {q : ℝ} (hq : 1 ≤ q)
    {δ : ℝ} (hδ1 : δ ≤ 1) (owner : Fin N → Fin J)
    (v c : Fin N → Space n) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (b : Fin J → Space n) (hnear : ∀ l, dist (c l) (b (owner l)) ≤ 2)
    (hsep : ∀ i j, i ≠ j → 2 ≤ dist (b i) (b j))
    (hv : ∀ l, ‖v l‖=1) :
    (∫ y, (weightedTubeOverlap δ v c weights y)^q) ≤ tubeGroupFactor n q*
      ∑ j, ∫ y, (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hi : Integrable (fun y => ∑ j,
      (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^q) :=
    integrable_finsetSum _ (fun j _ =>
      weightedTubeOverlap_power_integrable δ v c (groupWeights_nonneg owner hw j) hq0)
  have h := integral_mono (weightedTubeOverlap_power_integrable δ v c hw hq0)
    (hi.const_mul (tubeGroupFactor n q))
    (weightedTubeOverlap_spatial_power_le hq hδ1 owner v c hw b hnear hsep hv)
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ =>
    weightedTubeOverlap_power_integrable δ v c (groupWeights_nonneg owner hw j) hq0)] at h
  exact h

end KakeyaSharp.Graph
