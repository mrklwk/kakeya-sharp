/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

open Matrix
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

/-- The dimension-dependent version of the determinant/trace inequality
suffices for the ABP estimate. No strict positivity is needed. -/
theorem abs_det_le_trace_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    |A.det| ≤ A.trace ^ Fintype.card ι := by
  rw [abs_of_nonneg hA.det_nonneg, hA.isHermitian.det_eq_prod_eigenvalues,
    hA.isHermitian.trace_eq_sum_eigenvalues]
  calc
    ∏ i, hA.isHermitian.eigenvalues i ≤
        ∏ _i : ι, ∑ j, hA.isHermitian.eigenvalues j := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact hA.eigenvalues_nonneg i
      · intro i _
        exact Finset.single_le_sum (fun j _ ↦ hA.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = _ := by simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The same determinant/trace bound, invariantly for positive operators. -/
theorem abs_det_le_trace_pow_operator (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsPositive) :
    |A.det| ≤ (LinearMap.trace ℝ E A.toLinearMap) ^ Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hM := (LinearMap.posSemidef_toMatrix_iff b).mpr hA
  have h := abs_det_le_trace_pow hM
  simpa only [LinearMap.det_toMatrix, ← LinearMap.trace_eq_matrix_trace,
    Fintype.card_fin] using h

end OAI.Analysis.PDE.Elliptic
