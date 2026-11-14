/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.GraphTimeIntervals

@[expose] public section

/-! Head/tail Euclidean coordinates, with the actual Lebesgue measure
preserved when splitting one time coordinate from m spatial coordinates. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open MeasureTheory

def tail {m : ℕ} (x : Space (m+1)) : Space m :=
  WithLp.toLp 2 (fun j => x j.succ)

def insert {m : ℕ} (t : ℝ) (x : Space m) : Space (m+1) :=
  WithLp.toLp 2 (Fin.cons t (fun j => x j))

@[simp] theorem insert_zero {m : ℕ} (t : ℝ) (x : Space m) : insert t x 0=t := rfl
@[simp] theorem insert_succ {m : ℕ} (t : ℝ) (x : Space m) (j : Fin m) :
    insert t x j.succ=x j := rfl
@[simp] theorem tail_insert {m : ℕ} (t : ℝ) (x : Space m) : tail (insert t x)=x := rfl

theorem insert_head_tail {m : ℕ} (x : Space (m+1)) : insert (x 0) (tail x)=x := by
  ext j
  cases j using Fin.cases <;> rfl

@[simp] theorem tail_add {m : ℕ} (x y : Space (m+1)) : tail (x+y)=tail x+tail y := rfl
@[simp] theorem tail_sub {m : ℕ} (x y : Space (m+1)) : tail (x-y)=tail x-tail y := rfl
@[simp] theorem tail_smul {m : ℕ} (c : ℝ) (x : Space (m+1)) : tail (c • x)=c • tail x := rfl
@[simp] theorem tail_zero (m : ℕ) : tail (0 : Space (m+1))=0 := rfl

theorem norm_sq_head_tail {m : ℕ} (x : Space (m+1)) :
    ‖x‖^2=(x 0)^2+‖tail x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ,EuclideanSpace.real_norm_sq_eq]
  rfl

theorem abs_head_le_norm {m : ℕ} (x : Space (m+1)) : |x 0| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le x (0 : Fin (m+1))
  simpa only [Real.norm_eq_abs] using h

theorem norm_tail_le {m : ℕ} (x : Space (m+1)) : ‖tail x‖ ≤ ‖x‖ := by
  have h := norm_sq_head_tail x
  nlinarith [sq_nonneg (x 0),norm_nonneg x,norm_nonneg (tail x)]

theorem dist_tail_le {m : ℕ} (x y : Space (m+1)) : dist (tail x) (tail y) ≤ dist x y := by
  simpa only [dist_eq_norm,tail_sub] using norm_tail_le (x-y)

theorem norm_insert_zero {m : ℕ} (x : Space m) : ‖insert 0 x‖=‖x‖ := by
  have h := norm_sq_head_tail (insert 0 x)
  simp only [insert_zero,tail_insert,zero_pow (by norm_num : 2 ≠ 0),zero_add] at h
  nlinarith [norm_nonneg (insert 0 x),norm_nonneg x]

def coordinatesLinear (m : ℕ) : Space (m+1) ≃ₗ[ℝ] ℝ × Space m where
  toFun x := (x 0,tail x)
  invFun y := insert y.1 y.2
  left_inv := insert_head_tail
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinates (m : ℕ) : Space (m+1) ≃L[ℝ] ℝ × Space m :=
  (coordinatesLinear m).toContinuousLinearEquiv

theorem coordinates_measurePreserving (m : ℕ) :
    MeasurePreserving (coordinates m) volume volume := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin m))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin (m+1))))
  convert h using 1
  funext x
  apply Prod.ext
  · rfl
  · ext j
    simp [coordinates,coordinatesLinear,tail,MeasurableEquiv.piFinSuccAbove]
    rfl

theorem integral_coordinates (m : ℕ) (f : ℝ × Space m → ℝ) :
    (∫ x : Space (m+1), f (coordinates m x)) = ∫ y, f y :=
  (coordinates_measurePreserving m).integral_comp (coordinates m).toHomeomorph.measurableEmbedding f

end KakeyaSharp.Graph
