/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import Mathlib

@[expose] public section

/-! Differentiation over a fixed set contained in a compact set.
All domination is obtained from joint continuity on a compact parameter interval. -/
noncomputable section
namespace KakeyaSharp
open Set MeasureTheory Filter
open scoped Topology

theorem hasDerivAt_setIntegral_compact
    {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {S K : Set E}
    (hS : MeasurableSet S) (hK : IsCompact K) (hSK : S ⊆ K)
    {F F' : ℝ × E → ℝ} (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ t z, HasDerivAt (fun r => F (r,z)) (F' (t,z)) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ z in S, F (t,z) ∂μ) (∫ z in S, F' (t₀,z) ∂μ) t₀ := by
  have hk : IsCompact (Icc (t₀-1) (t₀+1) ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C,hC⟩ := hk.exists_bound_of_continuousOn hF'.continuousOn
  have hi (t : ℝ) : IntegrableOn (fun z => F (t,z)) S μ :=
    ((hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK).mono_set hSK
  have hi' : AEStronglyMeasurable (fun z => F' (t₀,z)) (μ.restrict S) :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hc : IntegrableOn (fun _ : E => C) S μ :=
    (integrableOn_const (μ := μ) (C := C) (s := K) (hK.measure_lt_top.ne)).mono_set hSK
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : t₀-1<t₀) (by linarith : t₀<t₀+1))
    (Filter.Eventually.of_forall (fun t => (hi t).aestronglyMeasurable))
    (hi t₀) hi' ?_ hc ?_).2
  · filter_upwards [ae_restrict_mem hS] with z hz
    intro t ht
    exact hC (t,z) ⟨⟨ht.1.le,ht.2.le⟩,hSK hz⟩
  · exact Filter.Eventually.of_forall (fun z t _ => hd t z)

end KakeyaSharp

