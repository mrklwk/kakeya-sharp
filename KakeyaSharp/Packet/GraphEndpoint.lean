/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.GlobalGraphTubes

@[expose] public section

/-! The closed scale range 0<delta<=1. At coarse scales a packing bound
and the individual tube volumes suffice, including delta=1. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

theorem normalizedTubeMoment_crude_bound {m N : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) :
    normalizedTubeMoment (128*δ) a v weights ≤
      (N : ℝ)^(inputExponent m-1)*(2*δ)^m*directionMass m*
        (∑ l, (weights l)^(inputExponent m)) := by
  have hs (t : ℝ) : sliceIntegral (128*δ) a v weights t ≤
      (N : ℝ)^(inputExponent m-1)*(2*δ)^m*directionMass m*
        (∑ l, (weights l)^(inputExponent m)) := by
    have h := integral_mono
      (sliceOverlap_power_integrable (128*δ) (inputExponent_ge_one hm) a v hw t)
      ((sliceMajorant_integrable (128*δ) (inputExponent m) a v weights t).const_mul _)
      (sliceOverlap_power_le (128*δ) (inputExponent_ge_one hm) a v hw t)
    rw [integral_const_mul,sliceMajorant_integral hm (by positivity : 0 < 128*δ)] at h
    have he : (128*δ)/64=2*δ := by ring
    simpa only [sliceIntegral,he,mul_assoc] using h
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (sliceIntegral_intervalIntegrable hm (by positivity : 0 < 128*δ) a v hw)
    intervalIntegrable_const (fun t _ => hs t)
  simpa only [normalizedTubeMoment,intervalIntegral.integral_const,sub_zero,one_smul] using h

def coarseGraphConstant (m : ℕ) : ℝ :=
  spatialGroupFactor m*(2 : ℝ)^m*directionMass m/Real.log 2

theorem coarseGraphConstant_pos (m : ℕ) : 0 < coarseGraphConstant m :=
  div_pos (mul_pos (mul_pos (spatialGroupFactor_pos m) (by positivity)) (directionMass_pos m))
    (Real.log_pos (by norm_num))

theorem normalizedTubeMoment_coarse_bound {m N : ℕ} (hm : 1 ≤ m)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhalf : 1/2 ≤ δ)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (hv : ∀ l, (∑ k, (v l k)^2) ≤ 1/16)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) :
    normalizedTubeMoment (128*δ) a v weights ≤
      coarseGraphConstant m*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  have hnear (l : Fin N) : dist (WithLp.toLp 2 (v l) : Space m) 0 ≤ 3*δ := by
    rw [dist_zero_right]
    have hv2 : ‖(WithLp.toLp 2 (v l) : Space m)‖^2 ≤ 1/16 := by
      simpa only [EuclideanSpace.real_norm_sq_eq] using hv l
    nlinarith [norm_nonneg (WithLp.toLp 2 (v l) : Space m)]
  have hcard : (N : ℝ) ≤ (8 : ℝ)^m := by
    have h := direction_cap_card_le hδ (fun l => (WithLp.toLp 2 (v l) : Space m)) hsep 0
    simpa only [Finset.filter_true_of_mem (fun l _ => hnear l),Finset.card_univ,Fintype.card_fin] using h
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg N) hcard
    (sub_nonneg.mpr (inputExponent_ge_one hm))
  have hS : 0 ≤ ∑ l, (weights l)^(inputExponent m) :=
    Finset.sum_nonneg (fun l _ => Real.rpow_nonneg (hw l) _)
  have hlog : Real.log 2 ≤ Real.log (2/δ) := Real.log_le_log (by norm_num)
    ((le_div_iff₀ hδ).mpr (by linarith))
  have hc : spatialGroupFactor m*(2 : ℝ)^m*directionMass m =
      coarseGraphConstant m*Real.log 2 := by
    unfold coarseGraphConstant
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  calc
    _ ≤ (N : ℝ)^(inputExponent m-1)*(2*δ)^m*directionMass m*
        (∑ l, (weights l)^(inputExponent m)) :=
      normalizedTubeMoment_crude_bound hm hδ a v hw
    _ ≤ spatialGroupFactor m*(2*δ)^m*directionMass m*
        (∑ l, (weights l)^(inputExponent m)) := by
      gcongr
      · exact (directionMass_pos m).le
      · exact hpow
    _ = (coarseGraphConstant m*Real.log 2)*δ^m*
        (∑ l, (weights l)^(inputExponent m)) := by rw [← hc,mul_pow]; ring
    _ ≤ _ := by gcongr; exact (coarseGraphConstant_pos m).le

theorem exists_globalGraphTube_closedScale_constant {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, (∑ j, (v l j)^2) ≤ 1/16) →
      (∀ i j, i ≠ j → δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) →
      normalizedTubeMoment (128*δ) a v weights ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  obtain ⟨C,hC,hbound⟩ := exists_globalGraphTube_constant hm
  refine ⟨C+coarseGraphConstant m,add_pos hC (coarseGraphConstant_pos m),?_⟩
  intro N δ hδ hδ1 a v weights hw hv hsep
  have hS : 0 ≤ ∑ l, (weights l)^(inputExponent m) :=
    Finset.sum_nonneg (fun l _ => Real.rpow_nonneg (hw l) _)
  have hL : 0 ≤ Real.log (2/δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  by_cases hlt : δ < 1
  · apply (hbound N δ hδ hlt a v weights hw hv hsep).trans
    gcongr
    exact le_add_of_nonneg_right (coarseGraphConstant_pos m).le
  · apply (normalizedTubeMoment_coarse_bound (by omega : 1 ≤ m) hδ hδ1
      (by linarith) a v hw hv hsep).trans
    gcongr
    exact le_add_of_nonneg_left hC.le

end KakeyaSharp.Packet
