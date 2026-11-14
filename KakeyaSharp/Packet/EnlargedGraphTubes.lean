/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.GraphCover

@[expose] public section

/-! The single-log weighted estimate with the radius 2 delta enlargement.
The directions are still delta-separated, and all constants are uniform
in scale, tube count, and nonnegative coefficients. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

/-- Since sliceOverlap uses radius scale/64, the scale 128*delta below
means graph tubes of radius 2*delta. -/
theorem exists_enlargedGraphTube_constant {m : ℕ} (hm : 1 ≤ m) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      ∀ (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, (∑ j, (a l j)^2) ≤ A) →
      (∀ l, (∑ j, (v l j)^2) ≤ 1/16) →
      (∀ i j, i ≠ j → δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) →
      normalizedTubeMoment (128*δ) a v weights ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  obtain ⟨J,b,hb,_,hcover⟩ := compact_finite_separated_net
    (isCompact_closedBall (0 : Space m) 2) (by norm_num : (0 : ℝ) < 1/64)
  have hJ : 0 < J := by
    obtain ⟨j,_⟩ := hcover 0 (by simp)
    exact lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  obtain ⟨C,hC,hbound⟩ := exists_normalizedTube_constant hm (by linarith : 0 ≤ 2*A+8)
  refine ⟨(J : ℝ)^(inputExponent m-1)*(J : ℝ)*C,
    mul_pos (mul_pos (Real.rpow_pos_of_pos hJr _) hJr) hC,?_⟩
  intro N δ hδ hδ1 a v weights hw ha hv hsep
  have h := normalizedTubeMoment_enlarged_le_sum (by omega : 1 ≤ m) hδ b hcover a v hw
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    hbound N δ hδ hδ1 (fun l => shiftedIntercept δ (a l) (b j)) v weights hw
      (fun l => shiftedIntercept_bound hδ hδ1.le (a l) (ha l) (hb j)) hv hsep)
  have hmul := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hJr.le (inputExponent m-1))
  apply h.trans
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hmul

end KakeyaSharp.Packet
