/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.WeakSuperharmonicLimit

@[expose] public section

/-! Pointwise convergence is required only inside the open test domain. -/
noncomputable section
namespace KakeyaSharp.Green
open Set Filter MeasureTheory InnerProductSpace Laplacian
open scoped Topology ContDiff

theorem weakSuperharmonicOn_of_tendsto_on {Ω : Set (Space 3)}
    (hΩ : IsOpen Ω)
    {F : ℕ → Space 3 → ℝ} {f : Space 3 → ℝ}
    (hF : ∀ n, WeakSuperharmonicOn Ω (F n))
    (hlim : ∀ p ∈ Ω, Tendsto (fun n => F n p) atTop (𝓝 (f p)))
    (hbound : ∀ K : Set (Space 3), IsCompact K → K ⊆ Ω →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n p, p ∈ K → |F n p| ≤ M) :
    WeakSuperharmonicOn Ω f := by
  refine ⟨?_, ?_⟩
  · apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
    intro K hKΩ hK
    obtain ⟨M,-,hM⟩ := hbound K hK hKΩ
    have hmeas (n : ℕ) : AEStronglyMeasurable (F n) (volume.restrict K) :=
      ((hF n).1.integrableOn_compact_subset hKΩ hK).aestronglyMeasurable
    have hfm : AEStronglyMeasurable f (volume.restrict K) := by
      apply aestronglyMeasurable_of_tendsto_ae atTop hmeas
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      exact hlim p (hKΩ hp)
    have hi : IntegrableOn (fun _ : Space 3 => M) K :=
      integrableOn_const hK.measure_lt_top.ne
    apply hi.mono' hfm
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    rw [Real.norm_eq_abs]
    exact le_of_tendsto (hlim p (hKΩ hp)).abs (Eventually.of_forall (fun n => hM n p hp))
  intro φ hφ hs hSupp hφ0
  obtain ⟨M,-,hMbound⟩ := hbound (tsupport φ) hs hSupp
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hi : Integrable (fun p => M * |laplacian φ p|) :=
    ((continuous_laplacian_space hφ2).abs.integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian_space hs).abs).const_mul M
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun p => F n p * laplacian φ p) volume :=
    ((hF n).2 φ hφ hs hSupp hφ0).1.aestronglyMeasurable
  have hdom (n : ℕ) (p : Space 3) : ‖F n p * laplacian φ p‖ ≤ M * |laplacian φ p| := by
    by_cases hp : p ∈ tsupport φ
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hMbound n p hp) (abs_nonneg _)
    · simp [laplacian_eq_zero_off_tsupport hp]
  have ht (p : Space 3) : Tendsto (fun n => F n p * laplacian φ p) atTop
      (𝓝 (f p * laplacian φ p)) := by
    by_cases hp : p ∈ tsupport φ
    · exact (hlim p (hSupp hp)).mul_const _
    · simp only [laplacian_eq_zero_off_tsupport hp, mul_zero]
      exact tendsto_const_nhds
  have hgmeas : AEStronglyMeasurable (fun p => f p * laplacian φ p) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas (Eventually.of_forall ht)
  have hgdom (p : Space 3) : ‖f p * laplacian φ p‖ ≤ M * |laplacian φ p| :=
    le_of_tendsto (ht p).norm (Eventually.of_forall (fun n => hdom n p))
  refine ⟨hi.mono' hgmeas (Eventually.of_forall hgdom), ?_⟩
  have hint := tendsto_integral_of_dominated_convergence (fun p => M * |laplacian φ p|)
    hmeas hi (fun n => Eventually.of_forall (hdom n)) (Eventually.of_forall ht)
  exact le_of_tendsto hint (Eventually.of_forall (fun n => ((hF n).2 φ hφ hs hSupp hφ0).2))

end KakeyaSharp.Green
