/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.GraphTimeIntervals

@[expose] public section

/-! Radius enlargement compatible with the slope-chart constants.
The graph radius is 8 delta while directions remain delta-separated. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

theorem sliceOverlap_mono_radius {m N : ℕ} {δ η : ℝ} (hδη : δ ≤ η)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (t : ℝ) (x : Space m) :
    sliceOverlap δ a v weights t x ≤ sliceOverlap η a v weights t x := by
  apply Finset.sum_le_sum
  intro l _
  by_cases h : dist x (graphAxis (a l) (v l) t) ≤ δ/64
  · have h' : dist x (graphAxis (a l) (v l) t) ≤ η/64 := by linarith
    simp only [h,h',ite_true,le_refl]
  · simp only [h,ite_false]
    split_ifs <;> first | exact hw l | rfl

theorem sliceIntegral_mono_radius {m N : ℕ} (hm : 1 ≤ m) {δ η : ℝ} (hδη : δ ≤ η)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (t : ℝ) : sliceIntegral δ a v weights t ≤ sliceIntegral η a v weights t := by
  exact integral_mono (sliceOverlap_power_integrable δ (inputExponent_ge_one hm) a v hw t)
    (sliceOverlap_power_integrable η (inputExponent_ge_one hm) a v hw t)
    (fun x => Real.rpow_le_rpow (sliceOverlap_nonneg δ a v hw t x)
      (sliceOverlap_mono_radius hδη a v hw t x) (le_trans (by norm_num) (inputExponent_ge_one hm)))

theorem normalizedTubeMoment_mono_radius {m N : ℕ} (hm : 1 ≤ m) {δ η : ℝ}
    (hδ : 0 < δ) (hδη : δ ≤ η)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) :
    normalizedTubeMoment δ a v weights ≤ normalizedTubeMoment η a v weights :=
  intervalIntegral.integral_mono_on (by norm_num)
    (sliceIntegral_intervalIntegrable hm hδ a v hw)
    (sliceIntegral_intervalIntegrable hm (hδ.trans_le hδη) a v hw)
    (fun t _ => sliceIntegral_mono_radius hm hδη a v hw t)

theorem exists_globalGraphTube_broad_constant {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, (∑ j, (v l j)^2) ≤ 1/16) →
      (∀ i j, i ≠ j → δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) →
      normalizedTubeMoment (512*δ) a v weights ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  obtain ⟨J,b,_,_,hcover⟩ := compact_finite_separated_net
    (isCompact_closedBall (0 : Space m) 2) (by norm_num : (0 : ℝ) < 1/64)
  have hJ : 0 < J := by
    obtain ⟨j,_⟩ := hcover 0 (by simp)
    exact lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  obtain ⟨C,hC,hbound⟩ := exists_globalGraphTube_closedScale_constant hm
  refine ⟨(J : ℝ)^(inputExponent m-1)*(J : ℝ)*C,
    mul_pos (mul_pos (Real.rpow_pos_of_pos hJr _) hJr) hC,?_⟩
  intro N δ hδ hδ1 a v weights hw hv hsep
  have h := normalizedTubeMoment_enlarged_le_sum (by omega : 1 ≤ m)
    (by positivity : 0 < 4*δ) b hcover a v hw
  have hscale : 128*(4*δ)=512*δ := by ring
  rw [hscale] at h
  have hlocal (j : Fin J) :
      normalizedTubeMoment (4*δ) (fun l => shiftedIntercept (4*δ) (a l) (b j)) v weights ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) :=
    (normalizedTubeMoment_mono_radius (by omega : 1 ≤ m)
      (by positivity : 0 < 4*δ) (by linarith : 4*δ ≤ 128*δ) _ v hw).trans
        (hbound N δ hδ hδ1 _ v weights hw hv hsep)
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hlocal j))
    (Real.rpow_nonneg hJr.le (inputExponent m-1))
  apply h.trans
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hsum

theorem exists_globalGraphTube_broad_timeInterval_constant {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N K : ℕ) (δ τ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, (∑ j, (v l j)^2) ≤ 1/16) →
      (∀ i j, i ≠ j → δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) →
      (∫ t in τ..(τ+K), sliceIntegral (512*δ) a v weights t) ≤
        (K : ℝ)*C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  obtain ⟨C,hC,hbound⟩ := exists_globalGraphTube_broad_constant hm
  refine ⟨C,hC,?_⟩
  intro N K δ τ hδ hδ1 a v weights hw hv hsep
  have hunit (s : ℝ) :
      (∫ t in s..(s+1), sliceIntegral (512*δ) a v weights t) ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
    have h := hbound N δ hδ hδ1 (fun l => timeShiftIntercept s (a l) (v l)) v weights hw hv hsep
    rwa [normalizedTubeMoment_timeShift] at h
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (f := sliceIntegral (512*δ) a v weights) (a := fun k : ℕ => τ+k) (n := K)
    (fun k _ => sliceIntegral_intervalIntegrable_all (by omega : 1 ≤ m)
      (by positivity : 0 < 512*δ) a v hw _ _)
  calc
    _ = ∑ k ∈ Finset.range K, ∫ t in (τ+k)..(τ+(k+1 : ℕ)), sliceIntegral (512*δ) a v weights t := by
      simpa only [Nat.cast_zero,add_zero] using he.symm
    _ ≤ ∑ _k ∈ Finset.range K, C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [Nat.cast_add,Nat.cast_one,← add_assoc] using hunit (τ+k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end KakeyaSharp.Packet
