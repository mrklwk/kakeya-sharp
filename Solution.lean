module

public import KakeyaSharp

/-! Proofs of the independently specified Palomar statements.
This module does not import Challenge. -/

open MeasureTheory
open scoped ENNReal RealInnerProductSpace BigOperators

@[expose] public section
noncomputable section
namespace KakeyaPalomar

/-- Euclidean n-space with its standard inner product and Lebesgue measure. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The canonical spherical measure induced by Lebesgue measure,
viewed as a measure on the ambient Euclidean space. -/
def sphereMeasure (n : ℕ) : Measure (Space n) :=
  (volume : Measure (Space n)).toSphere.map Subtype.val

/-- Open radius-δ neighborhood of the unit segment centered at x in direction ω.
All directions used in the tube estimate have Euclidean norm one. -/
def tube {n : ℕ} (δ : ℝ) (ω x : Space n) : Set (Space n) :=
  ⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ

/-- Average of |f| over a tube, maximized over every spatial center.
The denominator is its actual Lebesgue volume, including the end caps. -/
def kakeyaMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ) (ω : Space n) : ℝ≥0∞ :=
  ⨆ x : Space n, (∫⁻ y in tube δ ω x, ‖f y‖ₑ) / volume (tube δ ω x)

/-- Critical Kakeya maximal upper bound, uniformly over 0 < δ ≤ 1,
with logarithmic power (n-1)/n, in every integer dimension n ≥ 2. -/
theorem sharpMaximalBound {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : Space n → ℂ, MemLp f n volume →
        MemLp (kakeyaMaximal δ f) n (sphereMeasure n) ∧
        eLpNorm (kakeyaMaximal δ f) n (sphereMeasure n) ≤
          ENNReal.ofReal (C * Real.log (2 / δ) ^ (((n : ℝ) - 1) / n)) *
            eLpNorm f n volume := by
  change KakeyaSharp.SharpMaximalBound n
  exact KakeyaSharp.sharpMaximalBound_of_two_le hn

/-- Weighted tube upper bound with one logarithm. Directions are
δ-separated unit vectors, centers arbitrary, and coefficients nonnegative.
The radius is 2δ, and q = n/(n-1). -/
theorem sharpTubeBound {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ v x : Fin m → Space n, (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      ∀ a : Fin m → ℝ, (∀ i, 0 ≤ a i) →
        (∫ y, (∑ i, (tube (2 * δ) (v i) (x i)).indicator (fun _ ↦ a i) y) ^
          ((n : ℝ) / ((n : ℝ) - 1))) ≤
        C * Real.log (2 / δ) * δ ^ (n - 1) *
          ∑ i, a i ^ ((n : ℝ) / ((n : ℝ) - 1)) := by
  change KakeyaSharp.SharpTubeBound n
  exact KakeyaSharp.sharpTubeBound_of_two_le hn

end KakeyaPalomar
