/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Calculus.CurrentConservation
public import KakeyaSharp.Calculus.DirectionalHessian

@[expose] public section

/-! Restriction to a fixed parameter and commutation of actual derivatives.
These statements concern Frechet derivatives of the given function, rather
than a separately supplied array of formal derivatives. -/
noncomputable section
namespace KakeyaSharp.Calculus
open KakeyaSharp.Green KakeyaSharp.QuaternionAlgebra
open scoped ContDiff Matrix Matrix.Norms.Elementwise

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_directionalDerivative {n : ℕ∞ω} {f : E → F}
    (hf : ContDiff ℝ (n+1) f) (v : E) :
    ContDiff ℝ n (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (m := n) le_rfl).clm_apply contDiff_const

theorem fderiv_slice_right {f : P × E → F} {p : P} {x : E}
    (hf : DifferentiableAt ℝ f (p,x)) (v : E) :
    fderiv ℝ (fun y => f (p,y)) x v = fderiv ℝ f (p,x) (0,v) := by
  have h := hf.hasFDerivAt.comp x
    ((hasFDerivAt_const (𝕜 := ℝ) p x).prodMk (hasFDerivAt_id x))
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, _root_.zero_apply,
    ContinuousLinearMap.id_apply] using congrArg (fun L => L v) h.fderiv

theorem fderiv_slice_left {f : P × E → F} {p : P} {x : E}
    (hf : DifferentiableAt ℝ f (p,x)) (v : P) :
    fderiv ℝ (fun q => f (q,x)) p v = fderiv ℝ f (p,x) (v,0) := by
  have h := hf.hasFDerivAt.comp p
    ((hasFDerivAt_id (𝕜 := ℝ) p).prodMk (hasFDerivAt_const x p))
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, _root_.zero_apply,
    ContinuousLinearMap.id_apply] using congrArg (fun L => L v) h.fderiv

theorem secondDerivative_slice_right {f : P × E → ℝ}
    (hf : ContDiff ℝ 2 f) (p : P) (x a b : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (p,y))) x a b =
      fderiv ℝ (fderiv ℝ f) (p,x) (0,a) (0,b) := by
  have hs : ContDiff ℝ 2 (fun y => f (p,y)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  rw [← directional_twice hs]
  have he : (fun y => fderiv ℝ (fun z => f (p,z)) y b) =
      (fun y => fderiv ℝ f (p,y) (0,b)) := by
    funext y
    exact fderiv_slice_right (hf.differentiable (by norm_num) (p,y)) b
  rw [he, fderiv_slice_right
    ((contDiff_directionalDerivative (n := 1) hf (0,b)).differentiable (by norm_num) (p,x)),
    directional_twice hf]

theorem secondDerivative_directionalDerivative {f : E → ℝ}
    (hf : ContDiff ℝ 3 f) (x v a b : E) :
    fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ f y v)) x a b =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x v a b := by
  have hg : ContDiff ℝ 2 (fun y => fderiv ℝ f y v) :=
    contDiff_directionalDerivative (n := 2) hf v
  rw [← directional_twice hg]
  have he : (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y b) =
      (fun y => fderiv ℝ (fderiv ℝ f) y b v) := by
    funext y
    exact directional_twice (hf.of_le (by norm_num)) b v y
  rw [he, fderiv_second_apply hf.contDiffAt,
    thirdDerivative_swap23 hf.contDiffAt a b v,
    thirdDerivative_swap12 hf.contDiffAt a v b]

theorem fderiv_directionalHessian_apply {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : J → Q) (d : I × J → E)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x v : E) :
    fderiv ℝ (directionalHessian e d f) x v =
      directionalHessian e d (fun y => fderiv ℝ f y v) x := by
  rw [(hasFDerivAt_directionalHessian e d hf.contDiffAt).fderiv]
  change hessianMap e (fderiv ℝ (directionalRealHessian d f) x v) = _
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiable (by norm_num) x
  have he (a b : I × J) :=
    (hH.clm_apply (differentiableAt_const (d a))).clm_apply (differentiableAt_const (d b))
  have hmat : fderiv ℝ (directionalRealHessian d f) x v =
      fun a b => fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x v (d a) (d b) := by
    change (fderiv ℝ (fun y a b => fderiv ℝ (fderiv ℝ f) y (d a) (d b)) x v :
        (I × J) → (I × J) → ℝ) = _
    rw [fderiv_pi (fun a => differentiableAt_pi.mpr (he a))]
    ext a b
    simp only [ContinuousLinearMap.pi_apply]
    rw [fderiv_pi (he a)]
    exact fderiv_second_apply hf.contDiffAt _ _ _
  rw [hmat]
  unfold directionalHessian
  congr 1
  apply Matrix.ext
  intro a b
  exact (secondDerivative_directionalDerivative hf x v (d a) (d b)).symm

end KakeyaSharp.Calculus
