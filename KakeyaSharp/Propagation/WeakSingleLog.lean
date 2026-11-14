/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Propagation.SingleLog
public import KakeyaSharp.Propagation.LocalApproximation

@[expose] public section

/-! The single-log cylinder estimate for continuous weakly superharmonic
functions. Smooth approximation and both integral limits are proved here. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Propagation
open OAI.Analysis.PDE.Concentration MeasureTheory Set Metric Filter Laplacian
open scoped ContDiff Topology

def cylinderCompact (ρ : ℝ) : Set (Space 3) :=
  cylinderShell (-cylinderTimeEnd-1) (cylinderTimeEnd+1) (ρ/2) 4

theorem cylinderCompact_isCompact (ρ : ℝ) : IsCompact (cylinderCompact ρ) :=
  isCompact_cylinderShell _ _ _ _

theorem cylinderDomain_subset_compact (ρ : ℝ) : cylinderDomain ρ ⊆ cylinderCompact ρ := by
  intro x hx
  exact ⟨⟨hx.1.1.le,hx.1.2.le⟩,hx.2.1.le,hx.2.2.le⟩

theorem tracePoint_mem_compact {ρ t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ht : t ∈ Icc (1 : ℝ) 2) (θ : ℝ) :
    cylinderPoint t ρ θ ∈ cylinderCompact ρ :=
  cylinderPoint_mem_shell
    ⟨by dsimp [cylinderTimeEnd]; nlinarith [Real.pi_gt_three,ht.1],
     by dsimp [cylinderTimeEnd]; nlinarith [Real.pi_gt_three,ht.2]⟩
    ⟨by linarith,by linarith⟩ hρ.le

theorem inputPoint_mem_compact {ρ : ℝ} (hρ1 : ρ < 1) (θ : ℝ) :
    cylinderPoint 0 1 θ ∈ cylinderCompact ρ :=
  cylinderPoint_mem_shell
    ⟨by linarith [cylinderTimeEnd_pos],by linarith [cylinderTimeEnd_pos]⟩
    ⟨by linarith,by norm_num⟩ (by norm_num)

theorem cylinderTrace_tendsto {ρ M : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {F : ℕ → Space 3 → ℝ} {f : Space 3 → ℝ}
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hb : ∀ n x, x ∈ cylinderCompact ρ → ‖F n x‖ ≤ M)
    (hlim : ∀ x ∈ cylinderCompact ρ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ t in (1 : ℝ)..2, ∫ θ in (0 : ℝ)..(2*Real.pi),
      F n (cylinderPoint t ρ θ)) atTop
      (𝓝 (∫ t in (1 : ℝ)..2, ∫ θ in (0 : ℝ)..(2*Real.pi), f (cylinderPoint t ρ θ))) := by
  have hangle (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) :
      Tendsto (fun n => cylinderAngularAverage (F n) t ρ) atTop
        (𝓝 (cylinderAngularAverage f t ρ)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    · exact Eventually.of_forall (fun n =>
        (((contDiff_cylinder_radius_angle (hF n) t).continuous).comp
          (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => ae_of_all _ (fun θ _ =>
        hb n _ (tracePoint_mem_compact hρ hρ1 ht θ)))
    · exact intervalIntegrable_const
    · exact ae_of_all _ (fun θ _ => hlim _ (tracePoint_mem_compact hρ hρ1 ht θ))
  have hbound (n : ℕ) (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) :
      ‖cylinderAngularAverage (F n) t ρ‖ ≤ M*|2*Real.pi-(0 : ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ =>
      hb n _ (tracePoint_mem_compact hρ hρ1 ht θ))
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => M*|2*Real.pi-(0 : ℝ)|)
  · exact Eventually.of_forall (fun n =>
      ((contDiff_cylinderAngularAverage (hF n)).continuous.comp
        (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun n => ae_of_all _ (fun t ht =>
      hbound n t (by simpa using uIoc_subset_uIcc ht)))
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun t ht => hangle t (by simpa using uIoc_subset_uIcc ht))

/-- A fixed constant works for every continuous weakly superharmonic
function defined on an open neighborhood of the displayed compact cylinder. -/
theorem exists_weak_singleLog_cylinder_constant : ∃ C : ℝ, 0 < C ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ Ω : Set (Space 3), IsOpen Ω → cylinderCompact ρ ⊆ Ω →
    ∀ f : Space 3 → ℝ, ContinuousOn f Ω → Green.WeakSuperharmonicOn Ω f →
      (∀ x ∈ Ω, 0 ≤ f x) → ∀ θ : ℝ,
      (∫ t in (1 : ℝ)..2, ∫ φ in (0 : ℝ)..(2*Real.pi), f (cylinderPoint t ρ φ)) ≤
        C*(1+|Real.log ρ|)*f (cylinderPoint 0 1 θ) := by
  obtain ⟨C,hC,hc⟩ := exists_singleLog_cylinder_constant
  refine ⟨C,hC,?_⟩
  intro ρ hρ hρ1 Ω hΩ hKΩ f hf hw hn θ
  obtain ⟨F,M,hM,hF,hbounds,hlim⟩ := exists_local_superharmonic_approximation
    hΩ (cylinderCompact_isCompact ρ) hKΩ hf hw hn
  have hi (n : ℕ) :
      (∫ t in (1 : ℝ)..2, ∫ φ in (0 : ℝ)..(2*Real.pi), F n (cylinderPoint t ρ φ)) ≤
        C*(1+|Real.log ρ|)*F n (cylinderPoint 0 1 θ) :=
    hc ρ hρ hρ1 (F n) (hF n).contDiffOn
      (fun x hx => (hbounds n x (cylinderDomain_subset_compact ρ hx)).1)
      (fun x hx => (hbounds n x (cylinderDomain_subset_compact ρ hx)).2.1) θ
  exact le_of_tendsto_of_tendsto
    (cylinderTrace_tendsto hρ hρ1 hF (fun n x hx => (hbounds n x hx).2.2) hlim)
    ((hlim _ (inputPoint_mem_compact hρ1 θ)).const_mul (C*(1+|Real.log ρ|)))
    (Eventually.of_forall hi)

end KakeyaSharp.Propagation
