/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.DoubleDivergence
public import KakeyaSharp.Definitions
public import Mathlib.Analysis.InnerProductSpace.Laplacian

@[expose] public section

/-! The usual Euclidean Laplacian, compact test functions, and a precise
distributional nonpositivity predicate that includes integrability. -/
noncomputable section
namespace KakeyaSharp.Green
open Set MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff Topology

theorem laplacian_space_eq_sum {n : ℕ} (f : Space n → ℝ) (p : Space n) :
    laplacian f p = ∑ a, fderiv ℝ (fderiv ℝ f) p
      (EuclideanSpace.single a 1) (EuclideanSpace.single a 1) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

theorem continuous_laplacian_space {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (laplacian f) := by
  simp_rw [show laplacian f = fun p => ∑ a, fderiv ℝ (fderiv ℝ f) p
      (EuclideanSpace.single a 1) (EuclideanSpace.single a 1) from funext (laplacian_space_eq_sum f)]
  exact continuous_finsetSum _ (fun a _ => continuous_second_directional hf _ _)

theorem laplacian_eq_zero_off_tsupport {n : ℕ} {f : Space n → ℝ} {p : Space n}
    (hp : p ∉ tsupport f) : laplacian f p = 0 := by
  have hpD : p ∉ tsupport (fderiv ℝ f) := fun h => hp (tsupport_fderiv_subset ℝ h)
  have hDD : fderiv ℝ (fderiv ℝ f) p = 0 := fderiv_of_notMem_tsupport ℝ hpD
  rw [laplacian_space_eq_sum]
  simp [hDD]

theorem hasCompactSupport_laplacian_space {n : ℕ} {f : Space n → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (laplacian f) := by
  apply hf.mono'
  intro p hp
  by_contra hn
  exact hp (laplacian_eq_zero_off_tsupport hn)

theorem secondDeriv_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (p v : E) :
    deriv (deriv (fun t : ℝ => f (p+t•v))) 0 = fderiv ℝ (fderiv ℝ f) p v v := by
  have hl (t : ℝ) : HasDerivAt (fun s : ℝ => p+s•v) v t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add p
  have he : deriv (fun t : ℝ => f (p+t•v)) = (fun t => fderiv ℝ f (p+t•v) v) := by
    funext t
    exact ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  rw [he]
  have hD : ContDiff ℝ 1 (fun q => fderiv ℝ f q v) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h := ((hD.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt 0 (hl 0)).deriv
  simpa only [Function.comp_def, zero_smul, add_zero, directional_twice hf] using h

theorem integral_second_directional_test {n : ℕ} {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport φ) (v : Space n) :
    (∫ p, f p * fderiv ℝ (fderiv ℝ φ) p v v) =
      ∫ p, φ p * fderiv ℝ (fderiv ℝ f) p v v := by
  have hDφ : ContDiff ℝ 1 (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDf : ContDiff ℝ 1 (fun p => fderiv ℝ f p v) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h₁ := integral_directional_by_parts (μ := volume) (hφ.of_le (by norm_num)) hDf hs v
  have h₂ := integral_directional_by_parts (μ := volume) hDφ (hf.of_le (by norm_num)) (hs.fderiv_apply ℝ v) v
  simp only [directional_twice hf] at h₁
  simp only [directional_twice hφ] at h₂
  rw [h₁, h₂]
  simp only [neg_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => mul_comm _ _)

theorem integral_laplacian_test {n : ℕ} {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport φ) :
    (∫ p, f p * laplacian φ p) = ∫ p, φ p * laplacian f p := by
  have hi₁ (a : Fin n) : Integrable (fun p => f p * fderiv ℝ (fderiv ℝ φ) p
      (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)) := by
    apply (hf.continuous.mul (continuous_second_directional hφ _ _)).integrable_of_hasCompactSupport
    have h := ((hs.fderiv_apply ℝ (EuclideanSpace.single a 1)).fderiv_apply ℝ (EuclideanSpace.single a 1)).mul_left
      (f := f)
    simpa only [directional_twice hφ] using h
  have hi₂ (a : Fin n) : Integrable (fun p => φ p * fderiv ℝ (fderiv ℝ f) p
      (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)) :=
    (hφ.continuous.mul (continuous_second_directional hf _ _)).integrable_of_hasCompactSupport hs.mul_right
  simp_rw [laplacian_space_eq_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => hi₁ a), integral_finsetSum _ (fun a _ => hi₂ a)]
  apply Finset.sum_congr rfl
  intro a _
  exact integral_second_directional_test hφ hf hs _

/-- Distributional superharmonicity tested by nonnegative compactly supported
smooth functions. Integrability is part of the assertion. -/
def WeakSuperharmonicOn (Ω : Set (Space 3)) (f : Space 3 → ℝ) : Prop :=
  LocallyIntegrableOn f Ω ∧
  ∀ φ : Space 3 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∀ p, 0 ≤ φ p) → Integrable (fun p => f p * laplacian φ p) ∧
      (∫ p, f p * laplacian φ p) ≤ 0

theorem weakSuperharmonicOn_of_laplacian_nonpos {Ω : Set (Space 3)} {f : Space 3 → ℝ}
    (hf : ContDiff ℝ 2 f) (hΔ : ∀ p ∈ Ω, laplacian f p ≤ 0) : WeakSuperharmonicOn Ω f := by
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn Ω, ?_⟩
  intro φ hφ hs hΩ hφ0
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  refine ⟨(hf.continuous.mul (continuous_laplacian_space hφ2)).integrable_of_hasCompactSupport
    (hasCompactSupport_laplacian_space hs).mul_left, ?_⟩
  rw [integral_laplacian_test hφ2 hf hs]
  apply integral_nonpos_of_ae
  apply Filter.Eventually.of_forall
  intro p
  by_cases hp : p ∈ tsupport φ
  · exact mul_nonpos_of_nonneg_of_nonpos (hφ0 p) (hΔ p (hΩ hp))
  · simp [image_eq_zero_of_notMem_tsupport hp]

end KakeyaSharp.Green
