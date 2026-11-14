/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Dirichlet.Solution
public import OAI.Analysis.Fourier.WavePackets.Dirichlet.Existence
public import OAI.Analysis.Fourier.WavePackets.Dirichlet.Closed

@[expose] public section

/-! Packaging the fixed ball as upstream Dirichlet data, and descending
the resulting smooth solutions without changing the actual Hessian. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp.Dirichlet
open Set Matrix KakeyaSharp.Moore
open OAI.Analysis.Fourier.WavePackets
open scoped ContDiff ComplexOrder

def ballData (m : ℕ) {R : ℝ} (hR : 0 < R)
    (ρ : ThinSpace (m+1) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ z ∈ thinClosedBallAt R 0, 0 < ρ z) :
    PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots
      (split (m+1)) (lattice (m+1)) where
  dimension := by omega
  defining := defining R
  background := fun _ => 0
  density := fun x => ρ (project (m+1) x)
  transverse := thinClosedBallAt R 0
  compact := thinClosedBallAt_compact hR.le 0
  bounded := defining_bounded R
  defining_smooth := defining_smooth R
  background_smooth := contDiff_const
  density_smooth := hρ.comp (project (m+1)).contDiff
  defining_periodic := defining_periodic R
  background_periodic := fun _ _ => rfl
  density_periodic := lift_periodic ρ
  regular := defining_regular hR
  defining_positive := fun x _ => defining_hessian_pos R x
  background_nonnegative := by
    intro x _
    rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_const,
      OAI.LinearAlgebra.Moore.complexify_zero]
    exact Matrix.PosSemidef.zero
  background_degenerate := by
    intro x _
    rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_const]
    have hz := OAI.LinearAlgebra.Moore.mooreDet_smul (m+1) (0 : ℝ)
      (1 : Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    simpa using hz
  density_positive := fun x hx => hρpos _ ((defining_nonpos_iff R x).mp hx)

def descendBallSolution {m : ℕ} {R : ℝ} {hR : 0 < R}
    {ρ : ThinSpace (m+1) → ℝ} {hρ : ContDiff ℝ ∞ ρ}
    {hρpos : ∀ z ∈ thinClosedBallAt R 0, 0 < ρ z}
    (S : PeriodicQuaternionicSolution (ballData m hR ρ hρ hρpos)) :
    ThinDirichletSolution R 0 ρ := by
  have heq : ∀ x, defining R x ≤ 0 →
      OAI.LinearAlgebra.Moore.mooreDet (m+1)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian
          OAI.Analysis.Calculus.Quaternion.fourSlots S.u x) = ρ (project (m+1) x) := by
    simpa only [ballData, zero_add] using S.closed_equation
  have hpos : ∀ x, defining R x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian
          OAI.Analysis.Calculus.Quaternion.fourSlots S.u x)).PosDef := by
    simpa only [ballData, zero_add] using S.closed_positive
  have hi := solution_fourth_invariant (by omega : 1 ≤ m+1) hR
    (S.smooth.of_le (by simp)) S.periodic S.boundary hpos heq
  let u : ThinSpace (m+1) → ℝ := fun z => S.u (embed (m+1) z)
  have hu : ContDiff ℝ ∞ u := S.smooth.comp (embed (m+1)).contDiff
  have hc (z : ThinSpace (m+1)) (hz : z ∈ thinClosedBallAt R 0) :
      defining R (embed (m+1) z) ≤ 0 :=
    (defining_nonpos_iff R _).mpr (by simpa using hz)
  have hH (z : ThinSpace (m+1)) (hz : z ∈ thinClosedBallAt R 0) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian
        OAI.Analysis.Calculus.Quaternion.fourSlots S.u (embed (m+1) z) =
        thinQuaternionHessian u z := by
    simpa [u] using invariant_hessian_descends hR
      (S.smooth.of_le (by simp)) hi (embed (m+1) z) (hc z hz)
  have hp (z : ThinSpace (m+1)) (hz : z ∈ thinClosedBallAt R 0) :
      (complexify (thinQuaternionHessian u z)).PosDef := by
    rw [complexify_eq_upstream, ← hH z hz]
    exact hpos _ (hc z hz)
  have hh (z : ThinSpace (m+1)) :=
    thinQuaternionHessian_isHermitian ((hu.of_le (by simp)).contDiffAt (x := z))
  refine ⟨u,hu.of_le (by simp),⟨?_,?_,?_⟩,?_,?_⟩
  · intro z _
    exact (hu.of_le (by simp)).contDiffAt
  · intro z hz
    apply S.boundary
    simpa [ballData, defining] using sub_eq_zero.mpr hz
  · intro z hz
    exact (complexify_posSemidef_iff (hh z)).mp (hp z hz).posSemidef
  · intro z hz
    exact (complexify_posDef_iff (hh z)).mp (hp z hz)
  · intro z hz
    rw [mooreDet_eq_upstream, ← hH z hz, heq _ (hc z hz)]
    simp

@[simp] theorem descendBallSolution_u {m : ℕ} {R : ℝ} {hR : 0 < R}
    {ρ : ThinSpace (m+1) → ℝ} {hρ : ContDiff ℝ ∞ ρ}
    {hρpos : ∀ z ∈ thinClosedBallAt R 0, 0 < ρ z}
    (S : PeriodicQuaternionicSolution (ballData m hR ρ hρ hρpos))
    (z : ThinSpace (m+1)) :
    (descendBallSolution S).u z = S.u (embed (m+1) z) := rfl

end KakeyaSharp.Dirichlet
