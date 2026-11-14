module

public import Solution

/-! Semantic checks for the submitted maximal theorem.
The literal statement below uses canonical mathlib space and measure
definitions and expands the tube and maximal operator in place.
It is an audit of the upper bound, not a formalized matching lower bound. -/

open MeasureTheory
open scoped ENNReal

@[expose] public section
noncomputable section
namespace KakeyaSemanticAudit

theorem literal_maximal_statement {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℂ,
        MeasureTheory.MemLp f (n : ℝ≥0∞) MeasureTheory.volume →
        let K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun ω ↦
          ⨆ x : EuclideanSpace ℝ (Fin n),
            (∫⁻ y in (⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
              Metric.ball (x + t • ω) δ), ‖f y‖ₑ ∂MeasureTheory.volume) /
              MeasureTheory.volume
                (⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
                  Metric.ball (x + t • ω) δ)
        let σ := (MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).toSphere.map Subtype.val
        MeasureTheory.MemLp K (n : ℝ≥0∞) σ ∧
          MeasureTheory.eLpNorm K (n : ℝ≥0∞) σ ≤
            ENNReal.ofReal (C * Real.rpow (Real.log (2 / δ))
              (((n : ℝ) - 1) / (n : ℝ))) *
                MeasureTheory.eLpNorm f (n : ℝ≥0∞) MeasureTheory.volume := by
  exact KakeyaPalomar.sharpMaximalBound hn

theorem space_dimension (n : ℕ) :
    Module.finrank ℝ (KakeyaPalomar.Space n) = n := by
  simp [KakeyaPalomar.Space]

theorem extended_output_norm_is_identity (a : ℝ≥0∞) : ‖a‖ₑ = a := rfl

theorem sphere_total_mass (n : ℕ) :
    KakeyaPalomar.sphereMeasure n Set.univ =
      (n : ℝ≥0∞) * (volume : Measure (KakeyaPalomar.Space n)) (Metric.ball 0 1) := by
  rw [KakeyaPalomar.sphereMeasure, Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp [KakeyaPalomar.Space]

theorem sphere_mass_positive {n : ℕ} (hn : 2 ≤ n) :
    0 < KakeyaPalomar.sphereMeasure n Set.univ := by
  rw [sphere_total_mass]
  apply pos_iff_ne_zero.mpr
  apply mul_ne_zero
  · exact_mod_cast (show n ≠ 0 by omega)
  · exact ne_of_gt (Metric.measure_ball_pos volume (0 : KakeyaPalomar.Space n) (by norm_num))

theorem sphere_mass_finite (n : ℕ) :
    KakeyaPalomar.sphereMeasure n Set.univ < ∞ := by
  change ((volume : Measure (KakeyaPalomar.Space n)).toSphere.map Subtype.val) Set.univ < ∞
  exact measure_lt_top _ _

theorem sphere_supported_on_unit_vectors (n : ℕ) :
    ∀ᵐ ω ∂KakeyaPalomar.sphereMeasure n, ‖ω‖ = 1 := by
  change ∀ᵐ ω ∂(volume : Measure (KakeyaPalomar.Space n)).toSphere.map Subtype.val,
    ‖ω‖ = 1
  rw [ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) measurable_const)]
  exact Filter.Eventually.of_forall fun ω ↦ by
    simpa only [Metric.mem_sphere, dist_zero_right] using ω.property

theorem tube_membership {n : ℕ} (δ : ℝ) (ω x y : KakeyaPalomar.Space n) :
    y ∈ KakeyaPalomar.tube δ ω x ↔
      ∃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), dist y (x + t • ω) < δ := by
  simp [KakeyaPalomar.tube, Metric.mem_ball]

theorem actual_tube_volume_positive_finite {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (ω x : KakeyaPalomar.Space n) :
    0 < volume (KakeyaPalomar.tube δ ω x) ∧
      volume (KakeyaPalomar.tube δ ω x) < ∞ := by
  exact ⟨KakeyaSharp.volume_tube_pos hδ ω x, KakeyaSharp.volume_tube_lt_top δ ω x⟩

theorem includes_every_center {n : ℕ} (δ : ℝ)
    (f : KakeyaPalomar.Space n → ℂ) (ω x : KakeyaPalomar.Space n) :
    (∫⁻ y in KakeyaPalomar.tube δ ω x, ‖f y‖ₑ) /
      volume (KakeyaPalomar.tube δ ω x) ≤ KakeyaPalomar.kakeyaMaximal δ f ω := by
  exact le_iSup (fun x ↦ (∫⁻ y in KakeyaPalomar.tube δ ω x, ‖f y‖ₑ) /
    volume (KakeyaPalomar.tube δ ω x)) x

theorem indicator_of_tube_is_nontrivial {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (ω x : KakeyaPalomar.Space n) :
    1 ≤ KakeyaPalomar.kakeyaMaximal δ
      ((KakeyaPalomar.tube δ ω x).indicator (fun _ ↦ (1 : ℂ))) ω := by
  exact KakeyaSharp.one_le_kakeyaMaximal_indicator hδ (Set.Subset.refl _)

end KakeyaSemanticAudit

#print axioms KakeyaSemanticAudit.literal_maximal_statement
#print axioms KakeyaSemanticAudit.space_dimension
#print axioms KakeyaSemanticAudit.extended_output_norm_is_identity
#print axioms KakeyaSemanticAudit.sphere_total_mass
#print axioms KakeyaSemanticAudit.sphere_mass_positive
#print axioms KakeyaSemanticAudit.sphere_mass_finite
#print axioms KakeyaSemanticAudit.sphere_supported_on_unit_vectors
#print axioms KakeyaSemanticAudit.tube_membership
#print axioms KakeyaSemanticAudit.actual_tube_volume_positive_finite
#print axioms KakeyaSemanticAudit.includes_every_center
#print axioms KakeyaSemanticAudit.indicator_of_tube_is_nontrivial
