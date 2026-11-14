/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Transfer
public import KakeyaSharp.Dirichlet.Family

@[expose] public section

/-! Actual Dirichlet solutions for the regularized packet sources.
Existence, strict positivity, admissibility and local joint smooth
representatives are conclusions. No solution family is assumed. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set KakeyaSharp.Dirichlet KakeyaSharp.Moore
open scoped ContDiff Topology

theorem packetFamily_density_slice_smooth {m N : ℕ} {r : ℝ} (hr : 0 < r)
    (h : ℝ) (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m))) :
    ContDiff ℝ ∞ (fun z => currentDensity (packetFamily r h a v weights χ) (p,z)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (currentDensity_contDiffAt
    (packetFamily_contDiffAt hr h a v weights hχ (show 0 < radius (p,z) from hp))).comp z
      (contDiffAt_const.prodMk contDiffAt_id)

theorem packetFamily_density_nonneg {m N : ℕ} {r : ℝ} (hr : 0 < r)
    (h : ℝ) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    {χ : ℝ → ℝ} (hχ : ∀ t, 0 ≤ χ t)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    0 ≤ currentDensity (packetFamily r h a v weights χ) y := by
  rw [packetFamily_density]
  exact Finset.sum_nonneg (fun l _ => familyWeights_nonneg hr h a v hw hχ hy l)

/-- Every positive regularization of the packet source has a solution. -/
theorem packetFamily_regularized_solution {m N : ℕ} (hm : 1 ≤ m)
    {r R ε : ℝ} (hr : 0 < r) (hR : 0 < R) (hε : 0 < ε)
    (h : ℝ) (o : ThinSpace m) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχpos : ∀ t, 0 ≤ χ t)
    {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m))) :
    Nonempty (ThinDirichletSolution R o
      (fun z => currentDensity (packetFamily r h a v weights χ) (p,z)+ε)) := by
  apply exists_thinDirichletSolution hm hR o
    ((packetFamily_density_slice_smooth hr h a v weights hχ hp).add contDiff_const)
  intro z _
  exact add_pos_of_nonneg_of_pos (packetFamily_density_nonneg hr h a v hw hχpos hp) hε

/-- For the actual packet density on any open parameter domain avoiding
Y = 0, positive regularization gives spatially admissible solutions and
joint smooth local representatives on the closed spatial ball. -/
theorem packetFamily_regularized_solution_family {m N : ℕ} (hm : 1 ≤ m)
    {r R ε : ℝ} (hr : 0 < r) (hR : 0 < R) (hε : 0 < ε)
    (h : ℝ) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχpos : ∀ t, 0 ≤ χ t)
    (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    (hY : ∀ p ∈ Ω, 0 < radius (p,(0 : ThinSpace m))) :
    ∃ U : ThinCurrentSpace m → ℝ,
      (∀ p ∈ Ω, ContDiff ℝ 4 (thinSlice U p) ∧
        ThinAdmissibleAt R 0 (thinSlice U p) ∧
        (∀ z ∈ thinClosedBallAt R 0,
          mooreDet m (thinQuaternionHessian (thinSlice U p) z) =
            currentDensity (packetFamily r h a v weights χ) (p,z)+ε) ∧
        (∀ z ∈ thinClosedBallAt R 0, ∀ w ≠ 0,
          0 < quaternionForm (thinQuaternionHessian (thinSlice U p) z) w)) ∧
      (∀ p ∈ Ω, ∀ z ∈ thinClosedBallAt R 0,
        ∃ O : Set (ThinCurrentSpace m), IsOpen O ∧ (p,z) ∈ O ∧
          ∃ g : ThinCurrentSpace m → ℝ, ContDiffOn ℝ ∞ g O ∧
            ∀ q ∈ O, q.1 ∈ Ω → q.2 ∈ thinClosedBallAt R 0 → g q = U q) := by
  classical
  cases m with
  | zero => omega
  | succ m =>
    let A := packetFamily r h a v weights χ
    let ρ : ThinCurrentSpace (m+1) → ℝ :=
      fun y => if y.1 ∈ Ω then currentDensity A y+ε else 1
    have hs : ∀ p, ContDiff ℝ ∞ (fun z => ρ (p,z)) := by
      intro p
      by_cases hp : p ∈ Ω
      · simpa only [ρ,ite_eq_left hp] using
          (packetFamily_density_slice_smooth hr h a v weights hχ (hY p hp)).add
            (contDiff_const (c := ε))
      · simp only [ρ,ite_eq_right hp]
        exact contDiff_const
    have hp : ∀ p z, z ∈ thinClosedBallAt R 0 → 0 < ρ (p,z) := by
      intro p z _
      by_cases hp : p ∈ Ω
      · simp only [ρ,ite_eq_left hp]
        exact add_pos_of_nonneg_of_pos
          (packetFamily_density_nonneg hr h a v hw hχpos (hY p hp)) hε
      · simp [ρ,hp]
    have hρ : ContDiffOn ℝ ∞ ρ (Ω ×ˢ univ) := by
      intro y hy
      have hcur : ContDiffAt ℝ ∞ (fun q => currentDensity A q+ε) y :=
        (currentDensity_contDiffAt
          (packetFamily_contDiffAt hr h a v weights hχ
            (y := y) (hY y.1 hy.1))).add contDiffAt_const
      have he : ρ =ᶠ[nhds y] (fun q => currentDensity A q+ε) := by
        filter_upwards [(hΩ.preimage continuous_fst).mem_nhds hy.1] with q hq
        change q.1 ∈ Ω at hq
        simp [ρ,hq]
      exact (hcur.congr_of_eventuallyEq he).contDiffWithinAt
    obtain ⟨S,hS⟩ := exists_thinDirichlet_family hR hs hp hΩ hρ
    refine ⟨fun y => (S y.1).u y.2,?_,?_⟩
    · intro p hpΩ
      refine ⟨(S p).regularity,(S p).admissible,?_,(S p).positive⟩
      intro z hz
      change mooreDet (m+1) (thinQuaternionHessian (S p).u z) = _
      simpa only [ρ,A,ite_eq_left hpΩ] using (S p).equation z hz
    · exact hS

end KakeyaSharp.Packet
