/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.DirectionPacking
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-! Critical-power integration of the actual directional weight.
Only separation of the directions is required; the constant is independent
of the number of packets and of their weights. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

theorem directionWeight_measurable {m N : ℕ} (δ : ℝ)
    (v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    Measurable (directionWeight δ v weights) := by
  unfold directionWeight
  apply Finset.measurable_sum
  intro l _
  apply Measurable.ite _ measurable_const measurable_const
  exact isClosed_le (by fun_prop) continuous_const |>.measurableSet

def directionMajorant {m N : ℕ} (δ q : ℝ) (v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (α : Space m) : ℝ :=
  ∑ l, (closedBall (WithLp.toLp 2 (v l)) (3*δ)).indicator (fun _ => (weights l)^q) α

theorem directionMajorant_nonneg {m N : ℕ} (δ q : ℝ)
    (v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (α : Space m) : 0 ≤ directionMajorant δ q v weights α := by
  apply Finset.sum_nonneg
  intro l _
  exact Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (hw l) q) α

theorem directionWeight_rpow_le {m N : ℕ} {δ q : ℝ} (hδ : 0 < δ) (hq : 1 ≤ q)
    (v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (hsep : ∀ i j, i ≠ j →
      δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j)))
    (α : Space m) :
    (directionWeight δ v weights α)^q ≤
      ((8 : ℝ)^m)^(q-1)*directionMajorant δ q v weights α := by
  let s := Finset.univ.filter (fun l => dist (WithLp.toLp 2 (v l) : Space m) α ≤ 3*δ)
  have hcard : (s.card : ℝ) ≤ (8 : ℝ)^m :=
    direction_cap_card_le hδ (fun l => WithLp.toLp 2 (v l)) hsep α
  have hweight : directionWeight δ v weights α ≤ ∑ l ∈ s, weights l := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l _
    by_cases hc : (∑ j, (α j-v l j)^2) ≤ 5*δ^2
    · have he : dist (WithLp.toLp 2 (v l) : Space m) α^2 = ∑ j, (α j-v l j)^2 := by
        rw [dist_comm, dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
        rfl
      have hd : dist (WithLp.toLp 2 (v l) : Space m) α ≤ 3*δ := by
        have := dist_nonneg (x := (WithLp.toLp 2 (v l) : Space m)) (y := α)
        nlinarith [sq_nonneg δ]
      simp only [hc, hd, ite_true]
      rfl
    · simp only [hc, ite_false]
      split_ifs
      · exact hw l
      · rfl
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s
    (f := weights) hq (fun l _ => hw l)
  have hsum : 0 ≤ ∑ l ∈ s, (weights l)^q :=
    Finset.sum_nonneg (fun l _ => Real.rpow_nonneg (hw l) q)
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg s.card) hcard (sub_nonneg.mpr hq)
  have he : (∑ l ∈ s, (weights l)^q) = directionMajorant δ q v weights α := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    simp [Set.indicator, mem_closedBall, dist_comm]
  calc
    _ ≤ (∑ l ∈ s, weights l)^q :=
      Real.rpow_le_rpow (directionWeight_nonneg δ v hw α) hweight (by linarith)
    _ ≤ (s.card : ℝ)^(q-1)*(∑ l ∈ s, (weights l)^q) := hholder
    _ ≤ ((8 : ℝ)^m)^(q-1)*(∑ l ∈ s, (weights l)^q) :=
      mul_le_mul_of_nonneg_right hpow hsum
    _ = _ := by rw [he]

theorem directionMajorant_integrable {m N : ℕ} (δ q : ℝ)
    (v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    Integrable (directionMajorant δ q v weights) := by
  apply integrable_finsetSum
  intro l _
  exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall

theorem directionMajorant_integral {m N : ℕ} (hm : 1 ≤ m) {δ : ℝ}
    (hδ : 0 < δ) (q : ℝ) (v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    (∫ α, directionMajorant δ q v weights α) =
      ((3 : ℝ)^m*directionMass m)*δ^m*(∑ l, (weights l)^q) := by
  unfold directionMajorant
  rw [integral_finsetSum]
  · simp only [integral_indicator measurableSet_closedBall, integral_const,
      measureReal_restrict_apply_univ, smul_eq_mul,
      direction_closedBall_volume hm _ (by positivity : 0 ≤ 3*δ)]
    rw [← Finset.mul_sum, mul_pow]
    ring
  · intro l _
    exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall

def directionIntegralConstant (m : ℕ) (q : ℝ) : ℝ :=
  ((8 : ℝ)^m)^(q-1)*((3 : ℝ)^m*directionMass m)

theorem directionIntegralConstant_pos (m : ℕ) (q : ℝ) :
    0 < directionIntegralConstant m q := by
  unfold directionIntegralConstant
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (mul_pos (by positivity) (directionMass_pos m))

theorem directionWeight_rpow_integrable {m N : ℕ} {δ q : ℝ}
    (hδ : 0 < δ) (hq : 1 ≤ q) (v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (hsep : ∀ i j, i ≠ j →
      δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) :
    Integrable (fun α => (directionWeight δ v weights α)^q) := by
  have hi := (directionMajorant_integrable δ q v weights).const_mul (((8 : ℝ)^m)^(q-1))
  apply hi.mono' (((Real.continuous_rpow_const (by linarith : 0 ≤ q)).measurable.comp
    (directionWeight_measurable δ v weights)).aestronglyMeasurable)
  apply ae_of_all
  intro α
  change ‖(directionWeight δ v weights α)^q‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (directionWeight_nonneg δ v hw α) q)]
  exact directionWeight_rpow_le hδ hq v hw hsep α

theorem directionWeight_rpow_integral_le {m N : ℕ} (hm : 1 ≤ m) {δ q : ℝ}
    (hδ : 0 < δ) (hq : 1 ≤ q) (v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (hsep : ∀ i j, i ≠ j →
      δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) :
    (∫ α, (directionWeight δ v weights α)^q) ≤
      directionIntegralConstant m q*δ^m*(∑ l, (weights l)^q) := by
  have h := integral_mono (directionWeight_rpow_integrable hδ hq v hw hsep)
    ((directionMajorant_integrable δ q v weights).const_mul (((8 : ℝ)^m)^(q-1)))
    (directionWeight_rpow_le hδ hq v hw hsep)
  rw [integral_const_mul, directionMajorant_integral hm hδ] at h
  exact h.trans_eq (by unfold directionIntegralConstant; ring)

end KakeyaSharp.Packet
