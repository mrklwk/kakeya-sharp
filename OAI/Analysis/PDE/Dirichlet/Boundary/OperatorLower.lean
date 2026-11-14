/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import OAI.Analysis.Normed.Function.Holder.Banach.Composition

@[expose] public section

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem bounded_below_of_equiv_norm {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : E →L[ℝ] G) (L : E ≃L[ℝ] F) (h : ∀ x, ‖L x‖ = ‖A x‖) :
    ∃ C > 0, ∀ x, ‖x‖ ≤ C * ‖A x‖ := by
  refine ⟨1+‖L.symm.toContinuousLinearMap‖,by positivity,?_⟩
  intro x
  have hx := L.symm.toContinuousLinearMap.le_opNorm (L x)
  change ‖L.symm (L x)‖ ≤ _ at hx
  rw [L.symm_apply_apply,h] at hx
  exact hx.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end OAI.Analysis.PDE.Dirichlet
