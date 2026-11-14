/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Definitions

@[expose] public section

/- Adapted from openai/math, Apache-2.0, retrieved 2026-11-12.
Namespace and imports changed to isolate the elementary Kakeya infrastructure.
See SOURCES.json and LICENSE-OpenAI for provenance. -/
open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace KakeyaSharp

theorem isOpen_tube {n : ℕ} (δ : ℝ) (ω x : Space n) : IsOpen (KakeyaSharp.tube δ ω x) :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball

theorem measurableSet_tube {n : ℕ} (δ : ℝ) (ω x : Space n) :
    MeasurableSet (KakeyaSharp.tube δ ω x) := (isOpen_tube δ ω x).measurableSet

theorem mem_tube_iff {n : ℕ} {δ : ℝ} {ω x y : Space n} :
    y ∈ KakeyaSharp.tube δ ω x ↔
      ∃ t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2), dist y (x + t • ω) < δ := by
  simp [KakeyaSharp.tube, Metric.mem_ball]

theorem center_ball_subset_tube {n : ℕ} (δ : ℝ) (ω x : Space n) :
    Metric.ball x δ ⊆ KakeyaSharp.tube δ ω x := by
  intro y hy
  apply mem_tube_iff.mpr
  exact ⟨0, by norm_num, by simpa using hy⟩

theorem unitSegment_subset_tube {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (ω x : Space n) :
    KakeyaSharp.unitSegment ω x ⊆ KakeyaSharp.tube δ ω x := by
  rintro y ⟨t, ht, rfl⟩
  exact mem_tube_iff.mpr ⟨t, ht, by simpa using hδ⟩

theorem tube_mono {n : ℕ} {δ η : ℝ} (hδη : δ ≤ η) (ω x : Space n) :
    KakeyaSharp.tube δ ω x ⊆ KakeyaSharp.tube η ω x := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  exact mem_tube_iff.mpr ⟨t, ht, hyt.trans_le hδη⟩

/-- Directions that are `η` apart move corresponding points on the centered
unit segments by at most `η/2`. -/
theorem corresponding_segment_points_close {n : ℕ} {η t : ℝ} {ω v x : Space n}
    (ht : t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2)) (hωv : dist ω v ≤ η) :
    dist (x + t • ω) (x + t • v) ≤ η / 2 := by
  rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
  have ht' : |t| ≤ 1 / 2 := abs_le.mpr ht
  have hnorm : ‖ω - v‖ ≤ η := by simpa only [dist_eq_norm] using hωv
  calc
    |t| * ‖ω - v‖ ≤ (1 / 2) * ‖ω - v‖ :=
      mul_le_mul_of_nonneg_right ht' (norm_nonneg _)
    _ ≤ (1 / 2) * η := mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = η / 2 := by ring

/-- This is the geometric inclusion used to discretize the Kakeya maximal
operator in `sections/kakeya.tex`; it holds with the sharper `3δ/2` radius. -/
theorem tube_direction_inclusion {n : ℕ} {δ η : ℝ} {ω v x : Space n}
    (hωv : dist ω v ≤ η) : KakeyaSharp.tube δ ω x ⊆ KakeyaSharp.tube (δ + η / 2) v x := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  apply mem_tube_iff.mpr
  refine ⟨t, ht, ?_⟩
  calc
    dist y (x + t • v) ≤ dist y (x + t • ω) + dist (x + t • ω) (x + t • v) :=
      dist_triangle _ _ _
    _ < δ + η / 2 := add_lt_add_of_lt_of_le hyt (corresponding_segment_points_close ht hωv)

theorem tube_direction_inclusion_double {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    {ω v x : Space n} (hωv : dist ω v ≤ δ) : KakeyaSharp.tube δ ω x ⊆ KakeyaSharp.tube (2 * δ) v x :=
  (tube_direction_inclusion hωv).trans (tube_mono (by linarith) _ _)

theorem tube_subset_ball {n : ℕ} (δ : ℝ) (ω x : Space n) :
    KakeyaSharp.tube δ ω x ⊆ Metric.ball x (δ + ‖ω‖ / 2) := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  have hp : dist (x + t • ω) x ≤ ‖ω‖ / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hta : |t| ≤ 1 / 2 := abs_le.mpr ht
    nlinarith [mul_le_mul_of_nonneg_right hta (norm_nonneg ω)]
  exact lt_of_le_of_lt (dist_triangle _ _ _) (add_lt_add_of_lt_of_le hyt hp)

theorem volume_tube_lt_top {n : ℕ} (δ : ℝ) (ω x : Space n) :
    volume (KakeyaSharp.tube δ ω x) < ∞ :=
  (measure_mono (tube_subset_ball δ ω x)).trans_lt measure_ball_lt_top

theorem volume_tube_pos {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (ω x : Space n) :
    0 < volume (KakeyaSharp.tube δ ω x) :=
  (Metric.measure_ball_pos volume x hδ).trans_le (measure_mono (center_ball_subset_tube δ ω x))

/-- If a measurable set contains a whole tube, its indicator has maximal
average at least one in that direction. -/
theorem one_le_kakeyaMaximal_indicator {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A : Set (Space n)} {ω x : Space n} (hA : KakeyaSharp.tube δ ω x ⊆ A) :
    1 ≤ KakeyaSharp.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ))) ω := by
  have hi : (∫⁻ y in KakeyaSharp.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) =
      volume (KakeyaSharp.tube δ ω x) := by
    calc
      (∫⁻ y in KakeyaSharp.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) =
          ∫⁻ _y in KakeyaSharp.tube δ ω x, (1 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_tube δ ω x)] with y hy
        simp [Set.indicator_of_mem (hA hy)]
      _ = _ := by simp
  have hq : (∫⁻ y in KakeyaSharp.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) /
      volume (KakeyaSharp.tube δ ω x) = 1 := by
    rw [hi, ENNReal.div_self (ne_of_gt (volume_tube_pos hδ ω x)) (volume_tube_lt_top δ ω x).ne]
  exact hq.symm.le.trans (le_iSup (fun x ↦
    (∫⁻ y in KakeyaSharp.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) / volume (KakeyaSharp.tube δ ω x)) x)

end KakeyaSharp

