/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Dirichlet.Ball
public import OAI.Analysis.PDE.Dirichlet.ContinuousComparison

@[expose] public section

/-! Uniqueness makes every periodic solution invariant under arbitrary
translations in the added fourth coordinates when its source is invariant. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp.Dirichlet
open Set Matrix Filter
open scoped ContDiff Topology ComplexOrder

def fourthShift (m : ℕ) (w : Space m) : FullSpace m := (split m).symm (w,0)

@[simp] theorem project_fourthShift (m : ℕ) (w : Space m) :
    project m (fourthShift m w) = 0 := project_split_symm m w 0

@[simp] theorem defining_add_fourthShift {m : ℕ} (R : ℝ) (x : FullSpace m) (w : Space m) :
    defining R (x + fourthShift m w) = defining R x := by
  simp [defining]

theorem periodic_translate {m : ℕ} {ψ : FullSpace m → ℝ}
    (hp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (split m) (lattice m) ψ)
    (v : FullSpace m) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (split m) (lattice m) (fun x => ψ (x+v)) := by
  intro x l
  have he : (split m).symm (((split m) (x+v)).1 + (l : Space m), ((split m) (x+v)).2) =
      (split m).symm (((split m) x).1 + (l : Space m), ((split m) x).2) + v := by
    apply (split m).injective
    apply Prod.ext <;> simp [add_comm, add_left_comm]
  simpa only [he] using hp (x+v) l

theorem hessian_translate {m : ℕ} (ψ : FullSpace m → ℝ) (v x : FullSpace m) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian
      OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => ψ (y+v)) x =
    OAI.Analysis.PDE.Dirichlet.quaternionHessian
      OAI.Analysis.Calculus.Quaternion.fourSlots ψ (x+v) := by
  have he : fderiv ℝ (fun y => ψ (y+v)) = fun y => fderiv ℝ ψ (y+v) := by
    funext y
    exact fderiv_comp_add_right v
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian
  congr 1
  apply Matrix.ext
  intro i j
  simp only [OAI.Analysis.PDE.Dirichlet.realHessian, he, fderiv_comp_add_right]

theorem solution_fourth_invariant {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    {ρ : ThinSpace m → ℝ} {ψ : FullSpace m → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (split m) (lattice m) ψ)
    (hb : ∀ x, defining R x = 0 → ψ x = 0)
    (hpos : ∀ x, defining R x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian
          OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hdet : ∀ x, defining R x ≤ 0 →
      OAI.LinearAlgebra.Moore.mooreDet m
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian
          OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = ρ (project m x))
    (w : Space m) (x : FullSpace m) (hx : defining R x ≤ 0) :
    ψ (x+fourthShift m w) = ψ x := by
  have ht : ContDiff ℝ 2 (fun y => ψ (y+fourthShift m w)) :=
    hψ.comp (contDiff_id.add contDiff_const)
  apply OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_uniqueness_continuous_lattice hm
    (split m) (lattice m) (thinClosedBallAt_compact hR.le (0 : ThinSpace m))
    ht.contDiffOn hψ.contDiffOn ((defining_smooth R).of_le (by norm_num))
    ht.continuous.continuousOn hψ.continuous.continuousOn
    (defining_bounded R) (defining_periodic R) (periodic_translate hp _) hp
    (fun y _ => defining_hessian_pos R y) ?_ (fun y hy => hpos y hy.le) ?_ ?_ x hx
  · intro y hy
    rw [hessian_translate]
    apply hpos
    simpa only [defining_add_fourthShift] using hy.le
  · intro y hy
    rw [hessian_translate, hdet _ (by simpa only [defining_add_fourthShift] using hy.le),
      hdet _ hy.le]
    simp
  · intro y hy
    rw [hb _ (by simpa only [defining_add_fourthShift] using hy), hb _ hy]

end KakeyaSharp.Dirichlet
