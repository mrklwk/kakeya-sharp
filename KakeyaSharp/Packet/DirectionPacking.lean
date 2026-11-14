/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.InputDomination
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-! A dimension-only overlap bound for separated directional caps. -/
noncomputable section
set_option maxHeartbeats 800000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory MeasureTheory.Measure

def directionMass (m : ℕ) : ℝ := volume.real (ball (0 : Space m) 1)

theorem directionMass_pos (m : ℕ) : 0 < directionMass m :=
  ENNReal.toReal_pos (measure_ball_pos volume (0 : Space m) (by norm_num)).ne'
    measure_ball_lt_top.ne

theorem direction_ball_volume (m : ℕ) (x : Space m) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) = r^m*directionMass m := by
  simp only [measureReal_def, addHaar_ball_of_pos volume x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _), finrank_euclideanSpace, Fintype.card_fin,
    directionMass]

theorem direction_closedBall_volume {m : ℕ} (_hm : 1 ≤ m) (x : Space m)
    {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = r^m*directionMass m := by
  let : NeZero m := ⟨by omega⟩
  simpa [directionMass] using addHaar_real_closedBall volume x hr

theorem direction_cap_card_le {m N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v : Fin N → Space m) (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    (α : Space m) :
    ((Finset.univ.filter (fun l => dist (v l) α ≤ 3*δ)).card : ℝ) ≤ (8 : ℝ)^m := by
  let s := Finset.univ.filter (fun l => dist (v l) α ≤ 3*δ)
  have hd : PairwiseDisjoint (↑s) (fun l => ball (v l) (δ/2)) := by
    intro i _ j _ hij
    exact ball_disjoint_ball (by linarith [hsep i j hij])
  have hs : (⋃ l ∈ s, ball (v l) (δ/2)) ⊆ ball α (4*δ) := by
    intro x hx
    obtain ⟨l,hl,hx⟩ := mem_iUnion₂.mp hx
    have hl' : dist (v l) α ≤ 3*δ := (Finset.mem_filter.mp hl).2
    have hx' : dist x (v l) < δ/2 := hx
    change dist x α < 4*δ
    have := dist_triangle x (v l) α
    linarith
  have hvol := measureReal_mono (μ := volume) hs measure_ball_lt_top.ne
  rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)] at hvol
  simp_rw [direction_ball_volume m _ (by positivity : 0 < δ/2)] at hvol
  rw [direction_ball_volume m α (by positivity : 0 < 4*δ)] at hvol
  simp only [Finset.sum_const, nsmul_eq_mul] at hvol
  have hsmall : 0 < (δ/2)^m*directionMass m := mul_pos (pow_pos (by positivity) _) (directionMass_pos m)
  have he : (4*δ)^m*directionMass m = (8 : ℝ)^m*((δ/2)^m*directionMass m) := by
    rw [← mul_assoc, ← mul_pow]
    congr 2
    ring
  rw [he] at hvol
  exact (mul_le_mul_iff_left₀ hsmall).mp hvol

end KakeyaSharp.Packet
