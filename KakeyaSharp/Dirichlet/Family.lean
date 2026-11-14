/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Dirichlet.Data
public import OAI.Analysis.Fourier.WavePackets.General.Family.Regularity

@[expose] public section

/-! Smooth dependence on external parameters for the fixed thin ball.
The upstream family theorem supplies genuine solutions and local joint
representatives; parameter regularity is a conclusion. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Dirichlet
open Set OAI.Analysis.Fourier.WavePackets
open scoped ContDiff Topology

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z]

omit [FiniteDimensional ℝ Z] in
theorem ballData_locallyTrivial {m : ℕ} {R : ℝ} (hR : 0 < R)
    {ρ : Z × ThinSpace (m+1) → ℝ}
    (hs : ∀ p, ContDiff ℝ ∞ (fun z => ρ (p,z)))
    (hp : ∀ p z, z ∈ thinClosedBallAt R 0 → 0 < ρ (p,z))
    {Ω : Set Z} (hΩ : IsOpen Ω) (hρ : ContDiffOn ℝ ∞ ρ (Ω ×ˢ univ)) :
    LocallyTrivialDirichletData
      (fun p => ballData m hR (fun z => ρ (p,z)) (hs p) (hp p)) Ω := by
  refine ⟨hΩ,?_⟩
  intro p hpΩ
  refine ⟨Ω,Subset.rfl,⟨{
    open_parameter := hΩ
    base_mem := hpΩ
    forward := fun y => y.2
    backward := fun y => y.2
    sourceNeighborhood := Ω ×ˢ univ
    targetNeighborhood := Ω ×ˢ univ
    source_open := hΩ.prod isOpen_univ
    target_open := hΩ.prod isOpen_univ
    source_parameter := Subset.rfl
    target_parameter := Subset.rfl
    source_closed := fun y hy => ⟨hy.1,mem_univ _⟩
    target_closed := fun y hy => ⟨hy.1,mem_univ _⟩
    forward_smooth := contDiffOn_snd
    backward_smooth := contDiffOn_snd
    defining_smooth := (defining_smooth R).comp_contDiffOn contDiffOn_snd
    background_smooth := contDiffOn_const
    density_smooth := ?_
    forward_mem := fun _ hy => hy
    backward_mem := fun _ hy => hy
    backward_forward := fun _ _ => rfl
    forward_backward := fun _ _ => rfl
    forward_base := fun _ _ => rfl
    backward_base := fun _ _ => rfl
    forward_strict := fun _ _ _ hx => hx
    backward_strict := fun _ _ _ hx => hx
    forward_closed := fun _ _ _ hx => hx
    backward_closed := fun _ _ _ hx => hx
    forward_periodic := fun _ _ _ => rfl
    backward_periodic := fun _ _ _ => rfl
    backward_first := fun _ _ _ => rfl
    defining_transverse := ?_
  }⟩⟩
  · exact hρ.comp
      (contDiffOn_fst.prodMk ((project (m+1)).contDiff.comp_contDiffOn contDiffOn_snd))
      (fun y hy => ⟨hy.1,mem_univ _⟩)
  · intro p w z
    simp only [ballData, defining, project_split_symm]

/-- A smoothly varying positive source gives actual solutions together
with joint smooth representatives near every point of the closed ball. -/
theorem exists_thinDirichlet_family {m : ℕ} {R : ℝ} (hR : 0 < R)
    {ρ : Z × ThinSpace (m+1) → ℝ}
    (hs : ∀ p, ContDiff ℝ ∞ (fun z => ρ (p,z)))
    (hp : ∀ p z, z ∈ thinClosedBallAt R 0 → 0 < ρ (p,z))
    {Ω : Set Z} (hΩ : IsOpen Ω) (hρ : ContDiffOn ℝ ∞ ρ (Ω ×ˢ univ)) :
    ∃ S : (p : Z) → ThinDirichletSolution R 0 (fun z => ρ (p,z)),
      ∀ p ∈ Ω, ∀ z ∈ thinClosedBallAt R 0,
        ∃ O : Set (Z × ThinSpace (m+1)), IsOpen O ∧ (p,z) ∈ O ∧
          ∃ g : Z × ThinSpace (m+1) → ℝ, ContDiffOn ℝ ∞ g O ∧
            ∀ q ∈ O, q.1 ∈ Ω → q.2 ∈ thinClosedBallAt R 0 →
              g q = (S q.1).u q.2 := by
  obtain ⟨S,hS⟩ := exists_smooth_periodic_dirichlet_family
    (ballData_locallyTrivial hR hs hp hΩ hρ)
  refine ⟨fun p => descendBallSolution (S p),?_⟩
  intro p hpΩ z hz
  have hz' : defining R (embed (m+1) z) ≤ 0 :=
    (defining_nonpos_iff R _).mpr (by simpa using hz)
  obtain ⟨O,hO,hpz,g,hg,he⟩ := hS p hpΩ (embed (m+1) z) hz'
  let L : Z × ThinSpace (m+1) → Z × FullSpace (m+1) :=
    fun q => (q.1,embed (m+1) q.2)
  have hL : ContDiff ℝ ∞ L :=
    contDiff_fst.prodMk ((embed (m+1)).contDiff.comp contDiff_snd)
  refine ⟨L ⁻¹' O,hO.preimage hL.continuous,hpz,fun q => g (L q),?_,?_⟩
  · exact hg.comp hL.contDiffOn (fun _ hx => hx)
  · intro q hq hqΩ hqz
    exact he (L q) hq hqΩ
      ((defining_nonpos_iff R _).mpr (by simpa [L] using hqz))

end KakeyaSharp.Dirichlet
