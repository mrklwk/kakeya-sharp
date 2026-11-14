/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.TubeSlices

@[expose] public section

/-! The integral of tube overlap is bounded by a finite-net majorant,
without choosing a point where the overlap is maximal. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory

def coverMass (m : ℕ) : ℝ := (1/32 : ℝ)^m*directionMass m

theorem coverMass_pos (m : ℕ) : 0 < coverMass m := mul_pos (by positivity) (directionMass_pos m)

def coverMajorant {m N J : ℕ} (δ q : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (t : ℝ) (b : Fin J → Space m) (x : Space m) : ℝ :=
  ∑ j, (closedBall (b j) (δ/32)).indicator (fun _ => (coverWeight δ a v weights t (b j))^q) x

theorem coverMajorant_nonneg {m N J : ℕ} (δ q : ℝ) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (t : ℝ)
    (b : Fin J → Space m) (x : Space m) : 0 ≤ coverMajorant δ q a v weights t b x :=
  Finset.sum_nonneg (fun j _ => Set.indicator_nonneg
    (fun _ _ => Real.rpow_nonneg (coverWeight_nonneg δ a v hw t (b j)) q) x)

theorem sliceOverlap_le_coverMajorant {m N J : ℕ} {δ q : ℝ} (hδ : 0 < δ) (hq : 1 ≤ q)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (t : ℝ) (b : Fin J → Space m)
    (hcover : ∀ x, sliceOverlap δ a v weights t x ≠ 0 → ∃ j, dist x (b j) ≤ δ/32)
    (x : Space m) : (sliceOverlap δ a v weights t x)^q ≤ coverMajorant δ q a v weights t b x := by
  by_cases hx : sliceOverlap δ a v weights t x=0
  · rw [hx,Real.zero_rpow (by linarith : q ≠ 0)]
    exact coverMajorant_nonneg δ q a v hw t b x
  obtain ⟨j,hj⟩ := hcover x hx
  have h1 := Real.rpow_le_rpow (sliceOverlap_nonneg δ a v hw t x)
    (sliceOverlap_le_coverWeight hδ a v hw t hj) (by linarith : 0 ≤ q)
  have h2 := Finset.single_le_sum (s := Finset.univ)
    (f := fun k => (closedBall (b k) (δ/32)).indicator
      (fun _ => (coverWeight δ a v weights t (b k))^q) x)
    (fun k _ => Set.indicator_nonneg
      (fun _ _ => Real.rpow_nonneg (coverWeight_nonneg δ a v hw t (b k)) q) x)
    (Finset.mem_univ j)
  exact h1.trans (by simpa only [coverMajorant,
    Set.indicator_of_mem (show x ∈ closedBall (b j) (δ/32) from hj)] using h2)

theorem coverMajorant_integrable {m N J : ℕ} (δ q : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (t : ℝ) (b : Fin J → Space m) :
    Integrable (coverMajorant δ q a v weights t b) := by
  apply integrable_finsetSum
  intro j _
  exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall

theorem coverMajorant_integral {m N J : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (q : ℝ) (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) (t : ℝ)
    (b : Fin J → Space m) :
    (∫ x, coverMajorant δ q a v weights t b x) =
      coverMass m*δ^m*(∑ j, (coverWeight δ a v weights t (b j))^q) := by
  unfold coverMajorant
  rw [integral_finsetSum]
  · simp only [integral_indicator measurableSet_closedBall,integral_const,
      measureReal_restrict_apply_univ,smul_eq_mul,
      direction_closedBall_volume hm _ (by positivity : 0 ≤ δ/32)]
    rw [← Finset.mul_sum,div_pow]
    unfold coverMass
    simp only [div_eq_mul_inv, one_mul, inv_pow]
    ring
  · intro j _
    exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall

theorem sliceOverlap_integral_le_cover {m N J : ℕ} (hm : 1 ≤ m)
    {δ q : ℝ} (hδ : 0 < δ) (hq : 1 ≤ q)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (t : ℝ) (b : Fin J → Space m)
    (hcover : ∀ x, sliceOverlap δ a v weights t x ≠ 0 → ∃ j, dist x (b j) ≤ δ/32) :
    (∫ x, (sliceOverlap δ a v weights t x)^q) ≤
      coverMass m*δ^m*(∑ j, (coverWeight δ a v weights t (b j))^q) := by
  have h := integral_mono (sliceOverlap_power_integrable δ hq a v hw t)
    (coverMajorant_integrable δ q a v weights t b)
    (sliceOverlap_le_coverMajorant hδ hq a v hw t b hcover)
  rwa [coverMajorant_integral hm hδ] at h

end KakeyaSharp.Packet
