/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.GlobalChartTubes
public import KakeyaSharp.TubeReindex

@[expose] public section

/-! The dimension-only critical weighted overlap estimate for arbitrary
Euclidean tube families in every ambient dimension at least two. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open Set Metric MeasureTheory Packet

theorem weightedTubeMoment_partition_le {n N J : ℕ} {q : ℝ} (hq : 1 ≤ q)
    (δ : ℝ) (owner : Fin N → Fin J) (v c : Fin N → Space n)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) :
    (∫ y, (weightedTubeOverlap δ v c weights y)^q) ≤ ((J : ℝ)+1)^(q-1)*
      ∑ j, ∫ y, (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hi : Integrable (fun y => ∑ j,
      (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^q) :=
    integrable_finsetSum _ (fun j _ =>
      weightedTubeOverlap_power_integrable δ v c (groupWeights_nonneg owner hw j) hq0)
  have hpoint (y : Space n) :
      (weightedTubeOverlap δ v c weights y)^q ≤ ((J : ℝ)+1)^(q-1)*
        ∑ j, (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^q := by
    rw [weightedTubeOverlap_group_sum δ owner]
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ
      (f := fun j => weightedTubeOverlap δ v c (groupWeights owner weights j) y)
      hq (fun j _ => weightedTubeOverlap_nonneg δ v c (groupWeights_nonneg owner hw j) y)
    simp only [Finset.card_univ,Fintype.card_fin] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg J) (by linarith) (sub_nonneg.mpr hq))
    exact Finset.sum_nonneg (fun j _ => Real.rpow_nonneg
      (weightedTubeOverlap_nonneg δ v c (groupWeights_nonneg owner hw j) y) _)
  have h := integral_mono (weightedTubeOverlap_power_integrable δ v c hw hq0)
    (hi.const_mul (((J : ℝ)+1)^(q-1))) hpoint
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ =>
    weightedTubeOverlap_power_integrable δ v c (groupWeights_nonneg owner hw j) hq0)] at h
  exact h

theorem exists_allDirectionTube_constant {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v c : Fin N → Space (m+1)) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, ‖v l‖=1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      (∫ y, (weightedTubeOverlap δ v c weights y)^(inputExponent m)) ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_globalChartTube_constant hm
  obtain ⟨J,R,hcover⟩ := exists_finite_direction_charts m
  refine ⟨((J : ℝ)+1)^(inputExponent m-1)*C,
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) hC,?_⟩
  intro N δ hδ hδ1 v c weights hw hv hsep
  choose owner howner using (fun l => hcover (v l) (hv l))
  have hq := inputExponent_ge_one (m := m) (by omega)
  have hq0 : inputExponent m ≠ 0 := by linarith
  have hlocal (j : Fin J) :
      (∫ y, (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^(inputExponent m)) ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (groupWeights owner weights j l)^(inputExponent m)) := by
    let S := {l : Fin N // owner l=j}
    let K := Fintype.card S
    let e : Fin K ≃ S := (Fintype.equivFin S).symm
    simp_rw [weightedTubeOverlap_group_reindex δ owner v c weights j e]
    rw [groupWeights_power_reindex owner weights j e hq0,
      weightedTubeMoment_rotation (R j) δ (inputExponent m)]
    apply hbound K δ hδ hδ1 (fun k => R j (v (e k).val))
      (fun k => R j (c (e k).val)) (fun k => weights (e k).val)
    · exact fun k => hw _
    · intro k
      simpa only [LinearIsometryEquiv.norm_map] using hv (e k).val
    · intro k
      have h := howner (e k).val
      simpa only [(e k).property] using h
    · intro i k hik
      rw [LinearIsometryEquiv.dist_map]
      exact hsep _ _ (fun he => hik (e.injective (Subtype.ext he)))
  calc
    _ ≤ ((J : ℝ)+1)^(inputExponent m-1)*
        (∑ j, ∫ y, (weightedTubeOverlap δ v c (groupWeights owner weights j) y)^(inputExponent m)) :=
      weightedTubeMoment_partition_le hq δ owner v c hw
    _ ≤ ((J : ℝ)+1)^(inputExponent m-1)*(∑ j,
        C*Real.log (2/δ)*δ^m*(∑ l, (groupWeights owner weights j l)^(inputExponent m))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hlocal j))
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [← Finset.mul_sum,groupWeights_power_sum owner weights hq0]
      ring

end KakeyaSharp.Graph
