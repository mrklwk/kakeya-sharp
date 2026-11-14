/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Dirichlet.Ball
public import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Existence

@[expose] public section

/-! Unconditional periodic Dirichlet existence on the actual ball times
torus. The nonlinear solver is imported as a proved theorem, not an axiom. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp.Dirichlet
open Set Matrix
open scoped ContDiff ComplexOrder

theorem exists_periodic_ball_C4 (m : ℕ) {R : ℝ} (hR : 0 < R)
    {ρ : ThinSpace (m+1) → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ z ∈ thinClosedBallAt R 0, 0 < ρ z) :
    ∃ ψ : FullSpace (m+1) → ℝ, ContDiff ℝ 4 ψ ∧
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic (split (m+1)) (lattice (m+1)) ψ ∧
      (∀ x, defining R x = 0 → ψ x = 0) ∧
      (∀ x, defining R x ≤ 0 →
        (OAI.LinearAlgebra.Moore.complexify
          (OAI.Analysis.PDE.Dirichlet.quaternionHessian
            OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) ∧
      (∀ x, defining R x ≤ 0 →
        OAI.LinearAlgebra.Moore.mooreDet (m+1)
          (OAI.Analysis.PDE.Dirichlet.quaternionHessian
            OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = ρ (project (m+1) x)) := by
  refine OAI.Analysis.PDE.Dirichlet.exists_periodic_moore_dirichlet_C4
    (split (m+1)) (lattice (m+1)) (thinClosedBallAt_compact hR.le (0 : ThinSpace (m+1)))
    (r := defining R) (B₀ := fun _ => 0) (F := fun x => ρ (project (m+1) x))
    (defining_smooth R) contDiff_const (hρ.comp (project (m+1)).contDiff)
    (defining_periodic R) (fun _ _ => rfl) (lift_periodic ρ)
    (defining_bounded R) (defining_nonempty R) (defining_regular hR)
    (fun x _ => defining_hessian_pos R x) ?_ ?_
    (fun x hx => hρpos _ ((defining_nonpos_iff R x).mp hx))
  · intro x _
    rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_const,
      OAI.LinearAlgebra.Moore.complexify_zero]
    exact Matrix.PosSemidef.zero
  · intro x _
    rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_const]
    have hz := OAI.LinearAlgebra.Moore.mooreDet_smul (m+1) (0 : ℝ)
      (1 : Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    simpa using hz

end KakeyaSharp.Dirichlet
