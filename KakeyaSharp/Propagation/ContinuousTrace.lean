/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Propagation.WeakSingleLog

@[expose] public section

/-! Continuity of angular traces for continuous functions on a neighborhood
of the propagation cylinder. No differentiability of the value is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Propagation
open MeasureTheory Set OAI.Analysis.PDE.Concentration
open scoped ContDiff Topology

theorem continuous_cylinder_trace {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω) (hKΩ : cylinderCompact ρ ⊆ Ω)
    {f : Space 3 → ℝ} (hf : ContinuousOn f Ω) :
    ContinuousOn (fun t => cylinderAngularAverage f t ρ) (Icc (1 : ℝ) 2) ∧
      ∀ t ∈ Icc (1 : ℝ) 2,
        Continuous (fun θ => f (cylinderPoint t ρ θ)) := by
  obtain ⟨g,hg,he⟩ := exists_global_contDiff_extension 0 (cylinderCompact_isCompact ρ)
    (fun x hx => contDiffAt_zero.mpr ⟨Ω,hΩ.mem_nhds (hKΩ hx),hf⟩)
  have hH : Continuous (fun p : ℝ × ℝ => g (cylinderPoint p.1 ρ p.2)) :=
    hg.continuous.comp (contDiff_cylinderPoint.continuous.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
  have hangle : Continuous (fun t => cylinderAngularAverage g t ρ) := by
    have h := continuous_parametric_integral_of_continuous
      (μ := volume) (f := fun t θ : ℝ => g (cylinderPoint t ρ θ))
      hH (s := Icc (0 : ℝ) (2*Real.pi)) isCompact_Icc
    simpa only [cylinderAngularAverage,intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ 2*Real.pi),integral_Icc_eq_integral_Ioc] using h
  have heq (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) (θ : ℝ) :
      g (cylinderPoint t ρ θ)=f (cylinderPoint t ρ θ) :=
    (he _ (tracePoint_mem_compact hρ hρ1 ht θ)).self_of_nhds
  constructor
  · apply hangle.continuousOn.congr
    intro t ht
    exact intervalIntegral.integral_congr (fun θ _ => (heq t ht θ).symm)
  · intro t ht
    have heq' : (fun θ => f (cylinderPoint t ρ θ))=
        (fun θ => g (cylinderPoint t ρ θ)) := funext (fun θ => (heq t ht θ).symm)
    rw [heq']
    exact hH.comp (continuous_const.prodMk continuous_id)

end KakeyaSharp.Propagation
