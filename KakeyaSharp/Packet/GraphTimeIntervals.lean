/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.GraphEndpoint

@[expose] public section

/-! Arbitrary translated time intervals of integer length. The constant
in the single-log graph estimate remains independent of all intercepts. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set MeasureTheory

def timeShiftIntercept {m : ℕ} (τ : ℝ) (a v : Fin m → ℝ) : Fin m → ℝ :=
  fun k => a k+τ*v k

theorem graphAxis_timeShift {m : ℕ} (τ t : ℝ) (a v : Fin m → ℝ) :
    graphAxis (timeShiftIntercept τ a v) v t = graphAxis a v (τ+t) := by
  ext k
  simp [graphAxis,timeShiftIntercept]
  ring

theorem sliceOverlap_timeShift {m N : ℕ} (δ τ t : ℝ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) (x : Space m) :
    sliceOverlap δ (fun l => timeShiftIntercept τ (a l) (v l)) v weights t x =
      sliceOverlap δ a v weights (τ+t) x := by
  simp only [sliceOverlap,graphAxis_timeShift]

theorem sliceIntegral_timeShift {m N : ℕ} (δ τ t : ℝ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    sliceIntegral δ (fun l => timeShiftIntercept τ (a l) (v l)) v weights t =
      sliceIntegral δ a v weights (τ+t) := by
  simp only [sliceIntegral,sliceOverlap_timeShift]

theorem normalizedTubeMoment_timeShift {m N : ℕ} (δ τ : ℝ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    normalizedTubeMoment δ (fun l => timeShiftIntercept τ (a l) (v l)) v weights =
      ∫ t in τ..(τ+1), sliceIntegral δ a v weights t := by
  unfold normalizedTubeMoment
  simp only [sliceIntegral_timeShift,intervalIntegral.integral_comp_add_left,add_zero]

theorem sliceIntegral_intervalIntegrable_all {m N : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (s t : ℝ) :
    IntervalIntegrable (sliceIntegral δ a v weights) volume s t := by
  obtain ⟨C,hC⟩ := sliceIntegral_uniform_bound hm hδ a v hw
  rw [intervalIntegrable_iff']
  apply (integrableOn_const (μ := volume) (s := uIcc s t)
    isCompact_uIcc.measure_ne_top (C := C)).mono'
    (sliceIntegral_measurable hm δ a v weights).aestronglyMeasurable
  exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using hC t)

theorem exists_globalGraphTube_timeInterval_constant {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N K : ℕ) (δ τ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, (∑ j, (v l j)^2) ≤ 1/16) →
      (∀ i j, i ≠ j → δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) →
      (∫ t in τ..(τ+K), sliceIntegral (128*δ) a v weights t) ≤
        (K : ℝ)*C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  obtain ⟨C,hC,hbound⟩ := exists_globalGraphTube_closedScale_constant hm
  refine ⟨C,hC,?_⟩
  intro N K δ τ hδ hδ1 a v weights hw hv hsep
  have hunit (s : ℝ) :
      (∫ t in s..(s+1), sliceIntegral (128*δ) a v weights t) ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
    have h := hbound N δ hδ hδ1 (fun l => timeShiftIntercept s (a l) (v l)) v weights hw hv hsep
    rwa [normalizedTubeMoment_timeShift] at h
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (f := sliceIntegral (128*δ) a v weights) (a := fun k : ℕ => τ+k) (n := K)
    (fun k _ => sliceIntegral_intervalIntegrable_all (by omega : 1 ≤ m)
      (by positivity : 0 < 128*δ) a v hw _ _)
  calc
    _ = ∑ k ∈ Finset.range K, ∫ t in (τ+k)..(τ+(k+1 : ℕ)), sliceIntegral (128*δ) a v weights t := by
      simpa only [Nat.cast_zero,add_zero] using he.symm
    _ ≤ ∑ _k ∈ Finset.range K, C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [Nat.cast_add,Nat.cast_one,← add_assoc] using hunit (τ+k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end KakeyaSharp.Packet
