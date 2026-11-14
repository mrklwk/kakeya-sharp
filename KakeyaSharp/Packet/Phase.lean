/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import Mathlib

@[expose] public section

/-! The exact quadratic minimization in one coordinate of a compact packet.
The dimension-dependent phase is a finite sum of these scalar phases. -/
noncomputable section
namespace KakeyaSharp.Packet

def width (r s : ℝ) : ℝ := r+s
def denominator (r s τ : ℝ) : ℝ := (r+s)^2+τ^2

def center (r s τ a v x α : ℝ) : ℝ :=
  ((r+s)*(r*v+s*α)+τ*(x-a))/denominator r s τ

def residual (r s τ a v x α : ℝ) : ℝ :=
  ((r+s)*(x-a)-τ*(r*v+s*α))/denominator r s τ

def scalarEnergy (r s τ a v x α β w : ℝ) : ℝ :=
  r*(w-v)^2+(x-a-τ*w)^2/(r+s)+s*(α-w)^2+s*β^2

def scalarPhase (r s τ a v x α β : ℝ) : ℝ :=
  scalarEnergy r s τ a v x α β (center r s τ a v x α)

theorem denominator_pos {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (τ : ℝ) :
    0 < denominator r s τ := by
  unfold denominator
  positivity

theorem center_equations {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ a v x α : ℝ) :
    (r+s)*center r s τ a v x α - τ*residual r s τ a v x α = r*v+s*α ∧
    τ*center r s τ a v x α + (r+s)*residual r s τ a v x α = x-a := by
  have hD := (denominator_pos hr hs τ).ne'
  constructor <;> unfold center residual <;> field_simp [hD] <;> unfold denominator <;> ring

theorem scalarPhase_residual {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ a v x α β : ℝ) :
    scalarPhase r s τ a v x α β =
      r*(center r s τ a v x α-v)^2+(r+s)*(residual r s τ a v x α)^2+
        s*(α-center r s τ a v x α)^2+s*β^2 := by
  have hK : r+s ≠ 0 := (add_pos hr hs).ne'
  have hx := (center_equations hr hs τ a v x α).2
  unfold scalarPhase scalarEnergy
  rw [show x-a-τ*center r s τ a v x α = (r+s)*residual r s τ a v x α by linarith]
  field_simp

theorem scalarEnergy_gap {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ a v x α β w : ℝ) :
    scalarEnergy r s τ a v x α β w = scalarPhase r s τ a v x α β +
      denominator r s τ/(r+s)*(w-center r s τ a v x α)^2 := by
  have hK : r+s ≠ 0 := (add_pos hr hs).ne'
  obtain ⟨hc,hd⟩ := center_equations hr hs τ a v x α
  rw [scalarPhase_residual hr hs]
  unfold scalarEnergy denominator
  rw [show x-a-τ*w = (r+s)*residual r s τ a v x α -
    τ*(w-center r s τ a v x α) by linarith]
  field_simp
  linear_combination 2*(r+s)*(w-center r s τ a v x α)*hc

theorem scalarPhase_nonneg {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ a v x α β : ℝ) : 0 ≤ scalarPhase r s τ a v x α β := by
  rw [scalarPhase_residual hr hs]
  positivity

theorem scalarPhase_le_energy {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ a v x α β w : ℝ) : scalarPhase r s τ a v x α β ≤ scalarEnergy r s τ a v x α β w := by
  rw [scalarEnergy_gap hr hs]
  exact le_add_of_nonneg_right (mul_nonneg (div_pos (denominator_pos hr hs τ) (add_pos hr hs)).le (sq_nonneg _))

theorem scalarEnergy_eq_phase_iff {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ a v x α β w : ℝ) :
    scalarEnergy r s τ a v x α β w = scalarPhase r s τ a v x α β ↔
      w = center r s τ a v x α := by
  rw [scalarEnergy_gap hr hs, add_eq_left, mul_eq_zero]
  have h := (div_pos (denominator_pos hr hs τ) (add_pos hr hs)).ne'
  simp [h, sub_eq_zero]

theorem scalarPhase_completed_square {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ a v x α β : ℝ) :
    scalarPhase r s τ a v x α β =
      r*s/(r+s)*(α-v)^2+(r+s)/denominator r s τ*
        (x-a-τ*(r*v+s*α)/(r+s))^2+s*β^2 := by
  have hK : r+s ≠ 0 := (add_pos hr hs).ne'
  have hD := (denominator_pos hr hs τ).ne'
  rw [scalarPhase_residual hr hs]
  unfold center residual
  field_simp
  unfold denominator
  ring

end KakeyaSharp.Packet
