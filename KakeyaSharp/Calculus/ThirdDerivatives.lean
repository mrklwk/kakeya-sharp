/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Calculus.CofactorSymbol

@[expose] public section

/-! Actual third Fréchet derivatives and the derivative of the quaternionic Hessian. -/

noncomputable section
namespace KakeyaSharp.QuaternionAlgebra

open scoped Matrix Matrix.Norms.Elementwise

section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}

theorem thirdDerivative_swap12 (hf : ContDiffAt ℝ 3 f x) (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x v u w := by
  have h := ((hf.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt
    (by norm_num)).eq u v
  exact congrArg (fun L => L w) h

theorem fderiv_second_apply (hf : ContDiffAt ℝ 3 f x) (u v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) y v w) x u =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w := by
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply (hH.clm_apply (differentiableAt_const v))
    (differentiableAt_const w), fderiv_clm_apply hH (differentiableAt_const v)]
  simp

theorem thirdDerivative_swap23 (hf : ContDiffAt ℝ 3 f x) (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u w v := by
  have heq : (fun y => fderiv ℝ (fderiv ℝ f) y v w) =ᶠ[nhds x]
      (fun y => fderiv ℝ (fderiv ℝ f) y w v) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact (hy.isSymmSndFDerivAt (by norm_num)).eq v w
  have h := congrArg (fun L : E →L[ℝ] F => L u) (heq.fderiv_eq (𝕜 := ℝ))
  simpa only [fderiv_second_apply hf] using h

end General

end KakeyaSharp.QuaternionAlgebra

