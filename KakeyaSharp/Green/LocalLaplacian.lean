/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.DistributionalLaplacian
public import KakeyaSharp.LocalExtension

@[expose] public section

/-! Local smoothness suffices for the distributional Laplacian inequality.
No behavior of the function outside the open test domain is prescribed. -/
noncomputable section
namespace KakeyaSharp.Green
open Set Filter MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff Topology

theorem laplacian_congr_nhds {n : ℕ} {f g : Space n → ℝ} {p : Space n}
    (h : f =ᶠ[𝓝 p] g) : laplacian f p = laplacian g p := by
  simp only [laplacian_space_eq_sum, h.fderiv.fderiv_eq]

theorem secondDeriv_line_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p) (v : E) :
    deriv (deriv (fun t : ℝ => f (p+t•v))) 0 = fderiv ℝ (fderiv ℝ f) p v v := by
  obtain ⟨g, hg, he⟩ := exists_global_contDiff_extension 2 (isCompact_singleton (x := p))
    (fun x hx => by
      have hx' := mem_singleton_iff.mp hx
      subst x
      exact hf)
  have he₀ := he p (mem_singleton p)
  have hc : Continuous (fun t : ℝ => p+t•v) := by fun_prop
  have hl : (fun t : ℝ => g (p+t•v)) =ᶠ[𝓝 0] (fun t => f (p+t•v)) :=
    he₀.comp_tendsto (by simpa only [ContinuousAt, zero_smul, add_zero] using
      (hc.continuousAt : ContinuousAt (fun t : ℝ => p+t•v) 0))
  rw [← hl.deriv.deriv_eq, secondDeriv_line hg, he₀.fderiv.fderiv_eq]

theorem weakSuperharmonicOn_of_contDiffOn_laplacian_nonpos
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω) {f : Space 3 → ℝ}
    (hf : ContDiffOn ℝ 2 f Ω) (hΔ : ∀ p ∈ Ω, laplacian f p ≤ 0) :
    WeakSuperharmonicOn Ω f := by
  refine ⟨hf.continuousOn.locallyIntegrableOn hΩ.measurableSet, ?_⟩
  intro φ hφ hs hsub hφ0
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  obtain ⟨g, hg, he⟩ := exists_global_contDiff_extension 2 hs
    (fun p hp => (hf p (hsub hp)).contDiffAt (hΩ.mem_nhds (hsub hp)))
  have hprod : (fun p => f p * laplacian φ p) = (fun p => g p * laplacian φ p) := by
    funext p
    by_cases hp : p ∈ tsupport φ
    · rw [(he p hp).self_of_nhds]
    · simp only [laplacian_eq_zero_off_tsupport hp, mul_zero]
  rw [hprod]
  refine ⟨(hg.continuous.mul (continuous_laplacian_space hφ2)).integrable_of_hasCompactSupport
    (hasCompactSupport_laplacian_space hs).mul_left, ?_⟩
  rw [integral_laplacian_test hφ2 hg hs]
  apply integral_nonpos_of_ae
  apply Eventually.of_forall
  intro p
  change φ p * laplacian g p ≤ 0
  by_cases hp : p ∈ tsupport φ
  · rw [laplacian_congr_nhds (he p hp)]
    exact mul_nonpos_of_nonneg_of_nonpos (hφ0 p) (hΔ p (hsub hp))
  · simp only [image_eq_zero_of_notMem_tsupport hp, zero_mul, le_refl]

end KakeyaSharp.Green
