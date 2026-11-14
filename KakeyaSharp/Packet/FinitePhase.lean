/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Phase
public import KakeyaSharp.Packet.Quaternion

@[expose] public section

/-! Finite-dimensional packet phases and the sum of the coordinatewise
quaternionic tangency identities. -/
noncomputable section
namespace KakeyaSharp.Packet
open KakeyaSharp.QuaternionAlgebra

def phase {m : ℕ} (r s τ : ℝ) (a v x α β : Fin m → ℝ) : ℝ :=
  ∑ j, scalarPhase r s τ (a j) (v j) (x j) (α j) (β j)

def energy {m : ℕ} (r s τ : ℝ) (a v x α β w : Fin m → ℝ) : ℝ :=
  ∑ j, scalarEnergy r s τ (a j) (v j) (x j) (α j) (β j) (w j)

theorem energy_gap {m : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ : ℝ) (a v x α β w : Fin m → ℝ) :
    energy r s τ a v x α β w = phase r s τ a v x α β +
      denominator r s τ/(r+s)*∑ j, (w j-center r s τ (a j) (v j) (x j) (α j))^2 := by
  simp only [energy, phase, scalarEnergy_gap hr hs, Finset.sum_add_distrib, Finset.mul_sum]

theorem phase_nonneg {m : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ : ℝ) (a v x α β : Fin m → ℝ) : 0 ≤ phase r s τ a v x α β :=
  Finset.sum_nonneg (fun j _ => scalarPhase_nonneg hr hs τ (a j) (v j) (x j) (α j) (β j))

theorem phase_minimum {m : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ : ℝ) (a v x α β w : Fin m → ℝ) :
    phase r s τ a v x α β ≤ energy r s τ a v x α β w :=
  Finset.sum_le_sum (fun j _ => scalarPhase_le_energy hr hs τ (a j) (v j) (x j) (α j) (β j) (w j))

theorem phase_unique_minimizer {m : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ : ℝ) (a v x α β w : Fin m → ℝ) :
    energy r s τ a v x α β w = phase r s τ a v x α β ↔
      ∀ j, w j = center r s τ (a j) (v j) (x j) (α j) := by
  rw [energy_gap hr hs, add_eq_left, mul_eq_zero]
  have h := (div_pos (denominator_pos hr hs τ) (add_pos hr hs)).ne'
  simp only [h, false_or]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff, sub_eq_zero]

theorem phase_residual {m : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ : ℝ) (a v x α β : Fin m → ℝ) :
    phase r s τ a v x α β =
      r*(∑ j, (center r s τ (a j) (v j) (x j) (α j)-v j)^2)+
      (r+s)*(∑ j, (residual r s τ (a j) (v j) (x j) (α j))^2)+
      s*(∑ j, (α j-center r s τ (a j) (v j) (x j) (α j))^2)+s*(∑ j, (β j)^2) := by
  simp only [phase, scalarPhase_residual hr hs, Finset.sum_add_distrib, Finset.mul_sum]

theorem phase_completed_square {m : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ : ℝ) (a v x α β : Fin m → ℝ) :
    phase r s τ a v x α β =
      r*s/(r+s)*(∑ j, (α j-v j)^2)+(r+s)/denominator r s τ*
        (∑ j, (x j-a j-τ*(r*v j+s*α j)/(r+s))^2)+s*(∑ j, (β j)^2) := by
  simp only [phase, scalarPhase_completed_square hr hs, Finset.sum_add_distrib, Finset.mul_sum]

theorem phase_controls_deviations {m : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ : ℝ) (a v x α β : Fin m → ℝ) :
    r*(∑ j, (center r s τ (a j) (v j) (x j) (α j)-v j)^2) ≤ phase r s τ a v x α β ∧
    (r+s)*(∑ j, (residual r s τ (a j) (v j) (x j) (α j))^2) ≤ phase r s τ a v x α β ∧
    s*(∑ j, (α j-center r s τ (a j) (v j) (x j) (α j))^2) ≤ phase r s τ a v x α β ∧
    s*(∑ j, (β j)^2) ≤ phase r s τ a v x α β := by
  rw [phase_residual hr hs]
  have hc : 0 ≤ r*(∑ j, (center r s τ (a j) (v j) (x j) (α j)-v j)^2) := by positivity
  have hd : 0 ≤ (r+s)*(∑ j, (residual r s τ (a j) (v j) (x j) (α j))^2) := by positivity
  have hα : 0 ≤ s*(∑ j, (α j-center r s τ (a j) (v j) (x j) (α j))^2) := by positivity
  have hβ : 0 ≤ s*(∑ j, (β j)^2) := by positivity
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

def column {m : ℕ} (u v : ℝ) (α β c d : Fin m → ℝ) : Fin (m+1) → Q :=
  Fin.cases 1 (fun j => columnEntry u v (α j) (β j) (c j) (d j))

def phaseGradient {m : ℕ} (u v : ℝ) (α β c d : Fin m → ℝ) : Fin (m+1) → Q :=
  Fin.cases (∑ j, parameterPhaseGradient u v (α j) (β j) (c j) (d j))
    (fun j => spatialPhaseGradient u v (α j) (β j) (c j) (d j))

theorem column_phaseGradient_tangency {m : ℕ} {u v : ℝ} (huv : u^2+v^2=1)
    (α β c d : Fin m → ℝ) :
    (∑ j, star (column u v α β c d j)*phaseGradient u v α β c d j) = 0 := by
  simp only [column, phaseGradient, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    star_one, one_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun j _ => column_phase_tangency huv (α j) (β j) (c j) (d j))

end KakeyaSharp.Packet
