/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.EnlargedGraphTubes

@[expose] public section

/-! Finite spatial groups of graph tubes. Translation and restriction
preserve the actual overlap integrals and exactly partition coefficient mass. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

def groupWeights {N J : ℕ} (owner : Fin N → Fin J) (weights : Fin N → ℝ)
    (j : Fin J) (l : Fin N) : ℝ := if owner l=j then weights l else 0

def relativeIntercept {m N J : ℕ} (owner : Fin N → Fin J)
    (a : Fin N → Fin m → ℝ) (b : Fin J → Space m) (j : Fin J) (l : Fin N) : Fin m → ℝ :=
  fun k => if owner l=j then a l k-b j k else 0

theorem groupWeights_nonneg {N J : ℕ} (owner : Fin N → Fin J)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (j : Fin J) (l : Fin N) :
    0 ≤ groupWeights owner weights j l := by
  unfold groupWeights
  split_ifs <;> first | exact hw l | rfl

theorem groupWeights_power_sum {N J : ℕ} (owner : Fin N → Fin J)
    (weights : Fin N → ℝ) {q : ℝ} (hq : q ≠ 0) :
    (∑ j, ∑ l, (groupWeights owner weights j l)^q) = ∑ l, (weights l)^q := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  have he (j : Fin J) : (groupWeights owner weights j l)^q =
      if owner l=j then (weights l)^q else 0 := by
    unfold groupWeights
    split_ifs <;> simp [Real.zero_rpow hq]
  simp_rw [he]
  simp

theorem relativeIntercept_bound {m N J : ℕ} (owner : Fin N → Fin J)
    (a : Fin N → Fin m → ℝ) (b : Fin J → Space m)
    (hnear : ∀ l, dist (WithLp.toLp 2 (a l) : Space m) (b (owner l)) ≤ 2)
    (j : Fin J) (l : Fin N) :
    (∑ k, (relativeIntercept owner a b j l k)^2) ≤ 4 := by
  by_cases h : owner l=j
  · have hd := hnear l
    rw [h,dist_eq_norm] at hd
    have hs : ‖(WithLp.toLp 2 (a l) : Space m)-b j‖^2 ≤ 4 := by
      nlinarith [norm_nonneg ((WithLp.toLp 2 (a l) : Space m)-b j)]
    simpa [EuclideanSpace.real_norm_sq_eq,relativeIntercept,h] using hs
  · simp [relativeIntercept,h]

theorem sliceOverlap_group_sum {m N J : ℕ} (δ : ℝ) (owner : Fin N → Fin J)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) (t : ℝ) (x : Space m) :
    sliceOverlap δ a v weights t x =
      ∑ j, sliceOverlap δ a v (groupWeights owner weights j) t x := by
  unfold sliceOverlap groupWeights
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : dist x (graphAxis (a l) (v l) t) ≤ δ/64
  · simp [h]
  · simp [h]

theorem sliceOverlap_group_translate {m N J : ℕ} (δ : ℝ) (owner : Fin N → Fin J)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) (b : Fin J → Space m)
    (j : Fin J) (t : ℝ) (x : Space m) :
    sliceOverlap δ a v (groupWeights owner weights j) t x =
      sliceOverlap δ (relativeIntercept owner a b j) v
        (groupWeights owner weights j) t (x-b j) := by
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : owner l=j
  · have he : graphAxis (relativeIntercept owner a b j l) (v l) t =
        graphAxis (a l) (v l) t-b j := by
      ext k
      simp [graphAxis,relativeIntercept,h]
      ring
    rw [he,dist_sub_right]
  · simp [groupWeights,h]

theorem sliceIntegral_group_translate {m N J : ℕ} (δ : ℝ) (owner : Fin N → Fin J)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) (b : Fin J → Space m)
    (j : Fin J) (t : ℝ) :
    sliceIntegral δ a v (groupWeights owner weights j) t =
      sliceIntegral δ (relativeIntercept owner a b j) v (groupWeights owner weights j) t := by
  unfold sliceIntegral
  simp_rw [sliceOverlap_group_translate δ owner a v weights b j t]
  simpa only [sub_eq_neg_add] using integral_add_left_eq_self
    (μ := (volume : Measure (Space m)))
    (fun x => (sliceOverlap δ (relativeIntercept owner a b j) v
      (groupWeights owner weights j) t x)^(inputExponent m)) (-b j)

theorem normalizedTubeMoment_group_translate {m N J : ℕ} (δ : ℝ)
    (owner : Fin N → Fin J) (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    (b : Fin J → Space m) (j : Fin J) :
    normalizedTubeMoment δ a v (groupWeights owner weights j) =
      normalizedTubeMoment δ (relativeIntercept owner a b j) v (groupWeights owner weights j) := by
  unfold normalizedTubeMoment
  simp_rw [sliceIntegral_group_translate δ owner a v weights b j]

end KakeyaSharp.Packet
