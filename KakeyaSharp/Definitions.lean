/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import Mathlib

@[expose] public section

/-! Concrete definitions for the sharp Kakeya project.
No analytic estimate is declared as an axiom. -/

open MeasureTheory
open scoped ENNReal RealInnerProductSpace BigOperators

noncomputable section
namespace KakeyaSharp

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def sphereMeasure (n : ℕ) : Measure (Space n) :=
  (volume : Measure (Space n)).toSphere.map Subtype.val

instance sphereMeasure_isFinite (n : ℕ) : IsFiniteMeasure (sphereMeasure n) := by
  unfold sphereMeasure
  infer_instance

def unitSegment {n : ℕ} (ω x : Space n) : Set (Space n) :=
  {y | ∃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), y = x + t • ω}

/-- The open radius-δ neighborhood of the centered unit segment. -/
def tube {n : ℕ} (δ : ℝ) (ω x : Space n) : Set (Space n) :=
  ⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ

/-- Supremum over every spatial center, with the actual tube volume. -/
def kakeyaMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ) (ω : Space n) : ℝ≥0∞ :=
  ⨆ x : Space n, (∫⁻ y in tube δ ω x, ‖f y‖ₑ) / volume (tube δ ω x)

def overlapExponent (n : ℕ) : ℝ := (n : ℝ) / ((n : ℝ) - 1)
def logLoss (n : ℕ) (δ : ℝ) : ℝ :=
  Real.log (2 / δ) ^ (((n : ℝ) - 1) / n)

/-- A precise target proposition; this declaration is not a proof. -/
def SharpMaximalBound (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ f : Space n → ℂ, MemLp f n volume →
      MemLp (kakeyaMaximal δ f) n (sphereMeasure n) ∧
      eLpNorm (kakeyaMaximal δ f) n (sphereMeasure n) ≤
        ENNReal.ofReal (C * logLoss n δ) * eLpNorm f n volume

/-- The remaining analytic target: one logarithm in the weighted overlap integral.
Directions are δ-separated and tubes have radius 2δ, a fixed enlargement
convenient for discretizing the maximal operator. -/
def SharpTubeBound (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∀ v x : Fin m → Space n, (∀ i, ‖v i‖ = 1) →
    (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
    ∀ a : Fin m → ℝ, (∀ i, 0 ≤ a i) →
      (∫ y, (∑ i, (tube (2 * δ) (v i) (x i)).indicator (fun _ ↦ a i) y) ^
        overlapExponent n) ≤
      C * Real.log (2 / δ) * δ ^ (n - 1) * ∑ i, a i ^ overlapExponent n

end KakeyaSharp

