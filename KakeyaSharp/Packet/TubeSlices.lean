/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.OutputScaling
public import KakeyaSharp.DirectionNets

@[expose] public section

/-! Weighted slices of normalized tubes and the finite-net majorant. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

def graphAxis {m : ℕ} (a v : Fin m → ℝ) (t : ℝ) : Space m :=
  WithLp.toLp 2 a+t • WithLp.toLp 2 v

def sliceOverlap {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (t : ℝ) (x : Space m) : ℝ :=
  ∑ l, if dist x (graphAxis (a l) (v l) t) ≤ δ/64 then weights l else 0

def nearbyPackets {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    (t : ℝ) (b : Space m) : Finset (Fin N) :=
  Finset.univ.filter (fun l => dist b (graphAxis (a l) (v l) t) ≤ δ/16)

def coverWeight {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (t : ℝ) (b : Space m) : ℝ :=
  ∑ l ∈ nearbyPackets δ a v t b, weights l

theorem sliceOverlap_nonneg {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (t : ℝ) (x : Space m) :
    0 ≤ sliceOverlap δ a v weights t x := by
  apply Finset.sum_nonneg
  intro l _
  split_ifs <;> first | exact hw l | rfl

theorem coverWeight_nonneg {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (t : ℝ) (b : Space m) :
    0 ≤ coverWeight δ a v weights t b :=
  Finset.sum_nonneg (fun l _ => hw l)

theorem sliceOverlap_le_total {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (t : ℝ) (x : Space m) :
    sliceOverlap δ a v weights t x ≤ ∑ l, weights l := by
  apply Finset.sum_le_sum
  intro l _
  split_ifs <;> first | exact le_refl _ | exact hw l

theorem sliceOverlap_measurable {m N : ℕ} (δ : ℝ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    Measurable (fun y : ℝ × Space m => sliceOverlap δ a v weights y.1 y.2) := by
  apply Finset.measurable_sum
  intro l _
  apply Measurable.ite _ measurable_const measurable_const
  exact (isClosed_le (by unfold graphAxis; fun_prop) continuous_const).measurableSet

theorem sliceOverlap_le_coverWeight {m N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (t : ℝ) {x b : Space m} (hb : dist x b ≤ δ/32) :
    sliceOverlap δ a v weights t x ≤ coverWeight δ a v weights t b := by
  unfold sliceOverlap coverWeight nearbyPackets
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro l _
  by_cases hx : dist x (graphAxis (a l) (v l) t) ≤ δ/64
  · have hc : dist b (graphAxis (a l) (v l) t) ≤ δ/16 := by
      have h := dist_triangle b x (graphAxis (a l) (v l) t)
      rw [dist_comm b x] at h
      linarith
    simp only [hx,hc,ite_true,le_refl]
  · simp only [hx,ite_false]
    split_ifs <;> first | exact hw l | rfl

def sliceMajorant {m N : ℕ} (δ q : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (t : ℝ) (x : Space m) : ℝ :=
  ∑ l, (closedBall (graphAxis (a l) (v l) t) (δ/64)).indicator (fun _ => (weights l)^q) x

theorem sliceMajorant_integrable {m N : ℕ} (δ q : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (t : ℝ) : Integrable (sliceMajorant δ q a v weights t) := by
  apply integrable_finsetSum
  intro l _
  exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall

theorem sliceOverlap_power_le {m N : ℕ} (δ : ℝ) {q : ℝ} (hq : 1 ≤ q)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (t : ℝ) (x : Space m) :
    (sliceOverlap δ a v weights t x)^q ≤ (N : ℝ)^(q-1)*sliceMajorant δ q a v weights t x := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ
    (f := fun l => if dist x (graphAxis (a l) (v l) t) ≤ δ/64 then weights l else 0) hq
    (fun l _ => by split_ifs <;> first | exact hw l | rfl)
  have he (l : Fin N) : (if dist x (graphAxis (a l) (v l) t) ≤ δ/64 then weights l else 0)^q =
      if dist x (graphAxis (a l) (v l) t) ≤ δ/64 then (weights l)^q else 0 := by
    split_ifs <;> simp [Real.zero_rpow (by linarith : q ≠ 0)]
  simp_rw [he] at h
  simpa only [Finset.card_univ,Fintype.card_fin,sliceOverlap,sliceMajorant,Set.indicator,
    mem_closedBall] using h

theorem sliceOverlap_power_integrable {m N : ℕ} (δ : ℝ) {q : ℝ} (hq : 1 ≤ q)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (t : ℝ) : Integrable (fun x => (sliceOverlap δ a v weights t x)^q) := by
  apply ((sliceMajorant_integrable δ q a v weights t).const_mul ((N : ℝ)^(q-1))).mono'
    (((Real.continuous_rpow_const (by linarith : 0 ≤ q)).measurable.comp
      ((sliceOverlap_measurable δ a v weights).comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
  apply ae_of_all
  intro x
  change ‖(sliceOverlap δ a v weights t x)^q‖ ≤ (N : ℝ)^(q-1)*sliceMajorant δ q a v weights t x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (sliceOverlap_nonneg δ a v hw t x) q)]
  exact sliceOverlap_power_le δ hq a v hw t x

end KakeyaSharp.Packet
