/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.LocalExtension

@[expose] public section

/-! Extend a family near one compact spatial slice. Compactness provides a
single open parameter neighborhood on which all spatial germs are preserved. -/
noncomputable section
namespace KakeyaSharp
open Set Filter
open scoped Topology ContDiff

theorem exists_global_contDiff_extension_near_slice (n : ℕ)
    {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Ω : Set P} (hΩ : IsOpen Ω) {p : P} (hp : p ∈ Ω)
    {K : Set E} (hK : IsCompact K) {f : P × E → V}
    (hf : ∀ z ∈ K, ContDiffAt ℝ n f (p,z)) :
    ∃ g : P × E → V, ContDiff ℝ n g ∧
      ∃ W : Set P, IsOpen W ∧ p ∈ W ∧ W ⊆ Ω ∧
        ∀ q ∈ W, ∀ z ∈ K, g =ᶠ[𝓝 (q,z)] f := by
  obtain ⟨g, hg, he⟩ := exists_global_contDiff_extension n (E := P × E) (F := V) (f := f)
    ((isCompact_singleton (x := p)).prod hK)
    (fun y hy => by
      rcases y with ⟨q,z⟩
      obtain ⟨hq,hz⟩ := hy
      have hq' := mem_singleton_iff.mp hq
      change q = p at hq'
      subst q
      exact hf z hz)
  have hnear : ∀ᶠ q in 𝓝 p, ∀ z ∈ K, g =ᶠ[𝓝 (q,z)] f :=
    hK.eventually_forall_of_forall_eventually
      (fun z hz => (he (p,z) ⟨mem_singleton p,hz⟩).eventuallyEq_nhds)
  obtain ⟨W, hW, hWo, hpW⟩ := mem_nhds_iff.mp (hnear.and (hΩ.mem_nhds hp))
  exact ⟨g,hg,W,hWo,hpW,fun q hq => (hW hq).2,fun q hq => (hW hq).1⟩

end KakeyaSharp
