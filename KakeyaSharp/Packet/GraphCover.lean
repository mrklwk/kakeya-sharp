/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.NormalizedTubes

@[expose] public section

/-! A fixed finite cover enlarges graph tubes from radius delta/64 to
radius 2 delta without changing direction separation. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

def shiftedIntercept {m : ℕ} (δ : ℝ) (a : Fin m → ℝ) (b : Space m) : Fin m → ℝ :=
  fun j => a j+δ*b j

theorem graphAxis_shifted {m : ℕ} (δ t : ℝ) (a v : Fin m → ℝ) (b : Space m) :
    graphAxis (shiftedIntercept δ a b) v t = graphAxis a v t+δ • b := by
  ext j
  simp [graphAxis,shiftedIntercept]
  ring

theorem shiftedIntercept_bound {m : ℕ} {δ A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (a : Fin m → ℝ) (ha : (∑ j, (a j)^2) ≤ A)
    {b : Space m} (hb : b ∈ closedBall 0 2) :
    (∑ j, (shiftedIntercept δ a b j)^2) ≤ 2*A+8 := by
  have hb1 : ‖b‖ ≤ 2 := by simpa using hb
  have hb2 : (∑ j, (b j)^2) ≤ 4 := by
    rw [← EuclideanSpace.real_norm_sq_eq]
    nlinarith [norm_nonneg b]
  have hδ2 : δ^2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (f := fun j => (a j+δ*b j)^2) (g := fun j => 2*(a j)^2+2*δ^2*(b j)^2)
    (fun j _ => by nlinarith [sq_nonneg (a j-δ*b j)])
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hdb := mul_le_mul_of_nonneg_left hb2 (sq_nonneg δ)
  unfold shiftedIntercept
  nlinarith

theorem graph_point_covered {m J : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (b : Fin J → Space m)
    (hcover : ∀ y ∈ closedBall (0 : Space m) 2, ∃ j, dist y (b j) ≤ 1/64)
    (a v : Fin m → ℝ) (t : ℝ) {x : Space m}
    (hx : dist x (graphAxis a v t) ≤ (128*δ)/64) :
    ∃ j, dist x (graphAxis (shiftedIntercept δ a (b j)) v t) ≤ δ/64 := by
  let y : Space m := δ⁻¹ • (x-graphAxis a v t)
  have hxy : ‖x-graphAxis a v t‖ ≤ 2*δ := by rw [← dist_eq_norm]; linarith
  have hy : y ∈ closedBall 0 2 := by
    rw [mem_closedBall,dist_zero_right]
    dsimp [y]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)]
    calc
      _ ≤ δ⁻¹*(2*δ) := mul_le_mul_of_nonneg_left hxy (inv_nonneg.mpr hδ.le)
      _ = 2 := by field_simp
  obtain ⟨j,hj⟩ := hcover y hy
  refine ⟨j,?_⟩
  rw [graphAxis_shifted,dist_eq_norm]
  have he : x-(graphAxis a v t+δ • b j)=δ • (y-b j) := by
    dsimp [y]
    rw [smul_sub,smul_smul,mul_inv_cancel₀ hδ.ne',one_smul]
    abel
  rw [he,norm_smul,Real.norm_of_nonneg hδ.le,← dist_eq_norm]
  nlinarith [mul_le_mul_of_nonneg_left hj hδ.le]

theorem sliceOverlap_enlarged_le_sum {m N J : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (b : Fin J → Space m)
    (hcover : ∀ y ∈ closedBall (0 : Space m) 2, ∃ j, dist y (b j) ≤ 1/64)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (t : ℝ) (x : Space m) :
    sliceOverlap (128*δ) a v weights t x ≤
      ∑ j, sliceOverlap δ (fun l => shiftedIntercept δ (a l) (b j)) v weights t x := by
  unfold sliceOverlap
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro l _
  by_cases hx : dist x (graphAxis (a l) (v l) t) ≤ (128*δ)/64
  · obtain ⟨j,hj⟩ := graph_point_covered hδ b hcover (a l) (v l) t hx
    simp only [hx,ite_true]
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if dist x (graphAxis (shiftedIntercept δ (a l) (b j)) (v l) t) ≤ δ/64
        then weights l else 0) (fun j _ => by split_ifs <;> first | exact hw l | rfl)
      (Finset.mem_univ j)
    simpa only [hj,ite_true] using h
  · simp only [hx,ite_false]
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> first | exact hw l | rfl

theorem sliceIntegral_enlarged_le_sum {m N J : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (b : Fin J → Space m)
    (hcover : ∀ y ∈ closedBall (0 : Space m) 2, ∃ j, dist y (b j) ≤ 1/64)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (t : ℝ) :
    sliceIntegral (128*δ) a v weights t ≤
      (J : ℝ)^(inputExponent m-1)*
        ∑ j, sliceIntegral δ (fun l => shiftedIntercept δ (a l) (b j)) v weights t := by
  have hi : Integrable (fun x => ∑ j,
      (sliceOverlap δ (fun l => shiftedIntercept δ (a l) (b j)) v weights t x)^(inputExponent m)) :=
    integrable_finsetSum _ (fun j _ =>
      sliceOverlap_power_integrable δ (inputExponent_ge_one hm) _ v hw t)
  have h := integral_mono
    (sliceOverlap_power_integrable (128*δ) (inputExponent_ge_one hm) a v hw t)
    (hi.const_mul ((J : ℝ)^(inputExponent m-1))) (fun x => by
      have h1 := Real.rpow_le_rpow (sliceOverlap_nonneg (128*δ) a v hw t x)
        (sliceOverlap_enlarged_le_sum hδ b hcover a v hw t x)
        (le_trans (by norm_num) (inputExponent_ge_one hm))
      have h2 := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ
        (f := fun j => sliceOverlap δ (fun l => shiftedIntercept δ (a l) (b j)) v weights t x)
        (inputExponent_ge_one hm) (fun j _ => sliceOverlap_nonneg δ _ v hw t x)
      apply h1.trans
      simpa only [Finset.card_univ,Fintype.card_fin] using h2)
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ =>
    sliceOverlap_power_integrable δ (inputExponent_ge_one hm) _ v hw t)] at h
  exact h

theorem normalizedTubeMoment_enlarged_le_sum {m N J : ℕ} (hm : 1 ≤ m)
    {δ : ℝ} (hδ : 0 < δ) (b : Fin J → Space m)
    (hcover : ∀ y ∈ closedBall (0 : Space m) 2, ∃ j, dist y (b j) ≤ 1/64)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) :
    normalizedTubeMoment (128*δ) a v weights ≤ (J : ℝ)^(inputExponent m-1)*
      ∑ j, normalizedTubeMoment δ (fun l => shiftedIntercept δ (a l) (b j)) v weights := by
  have his : IntervalIntegrable (fun t => ∑ j,
      sliceIntegral δ (fun l => shiftedIntercept δ (a l) (b j)) v weights t) volume 0 1 := by
    convert IntervalIntegrable.sum (s := Finset.univ) (fun j _ =>
      sliceIntegral_intervalIntegrable hm hδ (fun l => shiftedIntercept δ (a l) (b j)) v hw) using 1
    ext t
    simp only [Finset.sum_apply]
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (sliceIntegral_intervalIntegrable hm (by positivity : 0 < 128*δ) a v hw)
    (his.const_mul ((J : ℝ)^(inputExponent m-1)))
    (fun t _ => sliceIntegral_enlarged_le_sum hm hδ b hcover a v hw t)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum
    (fun j _ => sliceIntegral_intervalIntegrable hm hδ
      (fun l => shiftedIntercept δ (a l) (b j)) v hw)] at h
  exact h

end KakeyaSharp.Packet
