/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.SpatialGroups

@[expose] public section

/-! Spatial localization with a dimension-only overlap factor. The
number of groups can grow with the tube locations, but the bound cannot. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

def spatialGroupFactor (m : ℕ) : ℝ := ((8 : ℝ)^m)^(inputExponent m-1)

theorem spatialGroupFactor_pos (m : ℕ) : 0 < spatialGroupFactor m :=
  Real.rpow_pos_of_pos (by positivity) _

theorem sliceOverlap_group_near {m N J : ℕ} {δ t : ℝ} (hδ1 : δ ≤ 1)
    (owner : Fin N → Fin J) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (b : Fin J → Space m)
    (hnear : ∀ l, dist (WithLp.toLp 2 (a l) : Space m) (b (owner l)) ≤ 2)
    (hv : ∀ l, (∑ k, (v l k)^2) ≤ 1/16) (ht : t ∈ Icc (0 : ℝ) 1)
    (j : Fin J) {x : Space m}
    (hx : sliceOverlap (128*δ) a v (groupWeights owner weights j) t x ≠ 0) :
    dist (b j) x ≤ 6 := by
  obtain ⟨l,_,hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  have haxis : dist x (graphAxis (a l) (v l) t) ≤ (128*δ)/64 := by
    by_contra hn
    simp only [hn,ite_false,ne_eq,not_true_eq_false] at hl
  have ho : owner l=j := by
    by_contra hn
    simp [groupWeights,hn] at hl
  have ha := hnear l
  rw [ho] at ha
  have hv2 : ‖(WithLp.toLp 2 (v l) : Space m)‖^2 ≤ 1/16 := by
    simpa only [EuclideanSpace.real_norm_sq_eq] using hv l
  have hvn : ‖(WithLp.toLp 2 (v l) : Space m)‖ ≤ 1/4 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (v l) : Space m)]
  have hshift : dist (graphAxis (a l) (v l) t) (WithLp.toLp 2 (a l)) ≤ 1/4 := by
    simp only [graphAxis,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.1]
    nlinarith [mul_le_mul_of_nonneg_right ht.2
      (norm_nonneg (WithLp.toLp 2 (v l) : Space m))]
  calc
    _ ≤ dist (b j) (WithLp.toLp 2 (a l))+
        (dist (WithLp.toLp 2 (a l)) (graphAxis (a l) (v l) t)+
          dist (graphAxis (a l) (v l) t) x) :=
      (dist_triangle (b j) (WithLp.toLp 2 (a l)) x).trans
        (add_le_add le_rfl (dist_triangle (WithLp.toLp 2 (a l)) (graphAxis (a l) (v l) t) x))
    _ ≤ 2+(1/4+(128*δ)/64) := add_le_add
      (by simpa only [dist_comm] using ha)
      (add_le_add (by simpa only [dist_comm] using hshift)
        (by simpa only [dist_comm] using haxis))
    _ ≤ 6 := by linarith

theorem sliceOverlap_spatial_power_le {m N J : ℕ} (hm : 1 ≤ m)
    {δ t : ℝ} (hδ1 : δ ≤ 1) (owner : Fin N → Fin J)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (b : Fin J → Space m)
    (hnear : ∀ l, dist (WithLp.toLp 2 (a l) : Space m) (b (owner l)) ≤ 2)
    (hsep : ∀ i j, i ≠ j → 2 ≤ dist (b i) (b j))
    (hv : ∀ l, (∑ k, (v l k)^2) ≤ 1/16) (ht : t ∈ Icc (0 : ℝ) 1)
    (x : Space m) :
    (sliceOverlap (128*δ) a v weights t x)^(inputExponent m) ≤ spatialGroupFactor m*
      ∑ j, (sliceOverlap (128*δ) a v (groupWeights owner weights j) t x)^(inputExponent m) := by
  let s := Finset.univ.filter (fun j => dist (b j) x ≤ 6)
  let g : Fin J → ℝ := fun j => sliceOverlap (128*δ) a v (groupWeights owner weights j) t x
  have hg (j : Fin J) : 0 ≤ g j :=
    sliceOverlap_nonneg (128*δ) a v (groupWeights_nonneg owner hw j) t x
  have hcard : (s.card : ℝ) ≤ (8 : ℝ)^m := by
    simpa only [show (3 : ℝ)*2=6 by norm_num] using
      direction_cap_card_le (by norm_num : (0 : ℝ) < 2) b hsep x
  have he : ∑ j, g j = ∑ j ∈ s, g j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · rfl
    · by_contra hn
      exact hj (sliceOverlap_group_near hδ1 owner a v weights b hnear hv ht j hn)
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s
    (f := g) (inputExponent_ge_one hm) (fun j _ => hg j)
  have hq := inputExponent_ge_one hm
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg s.card) hcard (sub_nonneg.mpr hq)
  have hsum : 0 ≤ ∑ j ∈ s, (g j)^(inputExponent m) :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (hg j) _)
  calc
    _ = (∑ j, g j)^(inputExponent m) := by rw [sliceOverlap_group_sum (128*δ) owner]
    _ = (∑ j ∈ s, g j)^(inputExponent m) := by rw [he]
    _ ≤ (s.card : ℝ)^(inputExponent m-1)*(∑ j ∈ s, (g j)^(inputExponent m)) := hh
    _ ≤ spatialGroupFactor m*(∑ j ∈ s, (g j)^(inputExponent m)) :=
      mul_le_mul_of_nonneg_right hpow hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_univ_sum_of_nonneg (fun j => Real.rpow_nonneg (hg j) _))
      (spatialGroupFactor_pos m).le

theorem sliceIntegral_spatial_le {m N J : ℕ} (hm : 1 ≤ m)
    {δ t : ℝ} (hδ1 : δ ≤ 1) (owner : Fin N → Fin J)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (b : Fin J → Space m)
    (hnear : ∀ l, dist (WithLp.toLp 2 (a l) : Space m) (b (owner l)) ≤ 2)
    (hsep : ∀ i j, i ≠ j → 2 ≤ dist (b i) (b j))
    (hv : ∀ l, (∑ k, (v l k)^2) ≤ 1/16) (ht : t ∈ Icc (0 : ℝ) 1) :
    sliceIntegral (128*δ) a v weights t ≤ spatialGroupFactor m*
      ∑ j, sliceIntegral (128*δ) a v (groupWeights owner weights j) t := by
  have hi : Integrable (fun x => ∑ j,
      (sliceOverlap (128*δ) a v (groupWeights owner weights j) t x)^(inputExponent m)) :=
    integrable_finsetSum _ (fun j _ =>
      sliceOverlap_power_integrable _ (inputExponent_ge_one hm) a v (groupWeights_nonneg owner hw j) t)
  have h := integral_mono
    (sliceOverlap_power_integrable (128*δ) (inputExponent_ge_one hm) a v hw t)
    (hi.const_mul (spatialGroupFactor m))
    (sliceOverlap_spatial_power_le hm hδ1 owner a v hw b hnear hsep hv ht)
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ =>
    sliceOverlap_power_integrable _ (inputExponent_ge_one hm) a v (groupWeights_nonneg owner hw j) t)] at h
  exact h

theorem normalizedTubeMoment_spatial_le {m N J : ℕ} (hm : 1 ≤ m)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (owner : Fin N → Fin J)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (b : Fin J → Space m)
    (hnear : ∀ l, dist (WithLp.toLp 2 (a l) : Space m) (b (owner l)) ≤ 2)
    (hsep : ∀ i j, i ≠ j → 2 ≤ dist (b i) (b j))
    (hv : ∀ l, (∑ k, (v l k)^2) ≤ 1/16) :
    normalizedTubeMoment (128*δ) a v weights ≤ spatialGroupFactor m*
      ∑ j, normalizedTubeMoment (128*δ) a v (groupWeights owner weights j) := by
  have hi : IntervalIntegrable (fun t => ∑ j,
      sliceIntegral (128*δ) a v (groupWeights owner weights j) t) volume 0 1 := by
    convert IntervalIntegrable.sum (s := Finset.univ) (fun j _ =>
      sliceIntegral_intervalIntegrable hm (by positivity : 0 < 128*δ) a v
        (groupWeights_nonneg owner hw j)) using 1
    ext t
    simp only [Finset.sum_apply]
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (sliceIntegral_intervalIntegrable hm (by positivity : 0 < 128*δ) a v hw)
    (hi.const_mul (spatialGroupFactor m))
    (fun t ht => sliceIntegral_spatial_le hm hδ1 owner a v hw b hnear hsep hv ht)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum
    (fun j _ => sliceIntegral_intervalIntegrable hm (by positivity : 0 < 128*δ) a v
      (groupWeights_nonneg owner hw j))] at h
  exact h

end KakeyaSharp.Packet
