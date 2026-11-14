/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.GraphSlopes

@[expose] public section

/-! Geometric containment of actual Euclidean unit-segment tubes in
graph tubes, with both the transverse error and end caps controlled. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open Set Metric

def intercept {m : ℕ} (c v : Space (m+1)) : Space m := tail c-c 0 • slope v

theorem graphAxis_intercept {m : ℕ} (c v : Space (m+1)) (t : ℝ) :
    Packet.graphAxis (intercept c v) (slope v) t=tail c+(t-c 0) • slope v := by
  ext j
  simp [Packet.graphAxis,intercept]
  ring

theorem graph_error_identity {m : ℕ} (c y v : Space (m+1)) (s : ℝ) (hv0 : 0 < v 0) :
    tail y-Packet.graphAxis (intercept c v) (slope v) (y 0) =
      tail (y-(c+s • v))-(y-(c+s • v)) 0 • slope v := by
  rw [graphAxis_intercept]
  ext j
  simp [tail,slope]
  field_simp [hv0.ne']
  ring

theorem tube_transverse_error {m : ℕ} {r : ℝ} {c y v : Space (m+1)}
    (hv0 : 0 < v 0) (hslope : ‖slope v‖ ≤ 1/4) (hy : y ∈ tube r v c) :
    dist (tail y) (Packet.graphAxis (intercept c v) (slope v) (y 0)) < 5*r/4 := by
  obtain ⟨s,_,hs⟩ := mem_tube_iff.mp hy
  let e := y-(c+s • v)
  have he : ‖e‖ < r := hs
  have hhead := abs_head_le_norm e
  have htail := norm_tail_le e
  have hsmul : ‖e 0 • slope v‖ ≤ ‖e‖/4 := by
    rw [norm_smul,Real.norm_eq_abs]
    have h := mul_le_mul hhead hslope (norm_nonneg (slope v)) (norm_nonneg e)
    linarith
  rw [dist_eq_norm,graph_error_identity c y v s hv0]
  calc
    _ ≤ ‖tail e‖+‖e 0 • slope v‖ := norm_sub_le _ _
    _ ≤ ‖e‖+‖e‖/4 := add_le_add htail hsmul
    _ < _ := by linarith

theorem tube_time_window {m : ℕ} {r : ℝ} {c y v : Space (m+1)}
    (hv : ‖v‖=1) (hy : y ∈ tube r v c) :
    y 0 ∈ Icc (c 0-r-1/2) (c 0+r+1/2) := by
  have hball := tube_subset_ball r v c hy
  have hh := abs_head_le_norm (y-c)
  have he : |y 0-c 0| < r+1/2 := by
    have hh' : |y 0-c 0| ≤ ‖y-c‖ := by simpa using hh
    exact hh'.trans_lt (by simpa only [mem_ball,dist_eq_norm,hv] using hball)
  have hl := (abs_lt.mp he).1
  have hu := (abs_lt.mp he).2
  constructor <;> linarith

theorem tube_near_north_in_graph {m : ℕ} {δ : ℝ} (hδ1 : δ ≤ 1)
    {c y v : Space (m+1)} (hv : ‖v‖=1) (hnear : dist v (north m) ≤ 1/16)
    (hc : c 0 ∈ Icc (-2 : ℝ) 2) (hy : y ∈ tube (2*δ) v c) :
    y 0 ∈ Icc (-5 : ℝ) 5 ∧
      dist (tail y) (Packet.graphAxis (intercept c v) (slope v) (y 0)) ≤ 5*δ/2 := by
  have hwindow := tube_time_window hv hy
  have hs := small_slope_of_near_north hnear
  have herror := tube_transverse_error hs.1 hs.2 hy
  exact ⟨⟨by linarith [hwindow.1,hc.1],by linarith [hwindow.2,hc.2]⟩,by linarith⟩

end KakeyaSharp.Graph
