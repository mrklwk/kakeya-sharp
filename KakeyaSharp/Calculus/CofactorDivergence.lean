/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Calculus.DirectionalHessian
public import KakeyaSharp.Moore.NullLagrangian

@[expose] public section

/-! The unconditional divergence identity for the actual Moore cofactor of a
quaternionic Hessian. No definiteness or nonsingularity hypothesis is used. -/

noncomputable section
namespace KakeyaSharp.QuaternionAlgebra

open KakeyaSharp.Moore
open scoped Matrix Matrix.Norms.Elementwise

theorem mooreCofactor_directionalHessian_divergence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {s : Type*} [Fintype s] [DecidableEq s]
    (e : s → Q) (d : Fin n × s → E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (b : Fin n) :
    strongDivergence e
      (fun p => fderiv ℝ (fun y => KakeyaSharp.Moore.mooreCofactor n (directionalHessian e d f y)) x (d p))
      b = 0 := by
  apply directionalHessian_conservation e d hf (KakeyaSharp.Moore.mooreCofactor n)
  · exact (KakeyaSharp.Moore.contDiff_mooreCofactor n 1).differentiable (by norm_num) _
  · intro g
    exact KakeyaSharp.Moore.mooreCofactor_fderiv_outer_vecMul _ g

end KakeyaSharp.QuaternionAlgebra

