/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinProfile
public import KakeyaSharp.QuaternionAlgebra

@[expose] public section

/-! Second derivatives used by the logarithmic thin-source test.
All Hessians in this file are actual iterated Fréchet derivatives. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace KakeyaSharp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem hessian_log {f : E → ℝ} (hf : ContDiff ℝ 2 f) {z : E}
    (hz : f z ≠ 0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) z v w =
      (f z)⁻¹ * fderiv ℝ (fderiv ℝ f) z v w -
        (f z ^ 2)⁻¹ * fderiv ℝ f z v * fderiv ℝ f z w := by
  have hf₁ := hf.differentiable (by norm_num)
  have hf₂ := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have he : fderiv ℝ (fun y => Real.log (f y)) =ᶠ[𝓝 z]
      fun y => (f y)⁻¹ • fderiv ℝ f y := by
    filter_upwards [hf.continuous.continuousAt.eventually_ne hz] with y hy
    exact fderiv.log (hf₁ y) hy
  have hi := (hasDerivAt_inv hz).comp_hasFDerivAt z (hf₁ z).hasFDerivAt
  have hh := (hi.smul (hf₂ z).hasFDerivAt).fderiv
  simp only [Function.comp_def, Pi.smul_def'] at hh
  rw [he.fderiv_eq, hh]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem hessian_sub_at {f g : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y - g y)) z v w =
      fderiv ℝ (fderiv ℝ f) z v w - fderiv ℝ (fderiv ℝ g) z v w := by
  have he : fderiv ℝ (fun y => f y - g y) =ᶠ[𝓝 z]
      fun y => fderiv ℝ f y - fderiv ℝ g y := by
    filter_upwards [hf.eventually (by norm_num),
      hg.eventually (by norm_num)] with y hfy hgy
    exact ((hfy.differentiableAt (by norm_num)).hasFDerivAt.sub
      (hgy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hf₂ := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg₂ := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh := (hf₂.hasFDerivAt.sub hg₂.hasFDerivAt).fderiv
  simp only [Pi.sub_def] at hh
  rw [he.fderiv_eq, hh]
  rfl

def projectedQuadratic (L : E →L[ℝ] F) (a c : ℝ) (z : E) : ℝ :=
  a + c * ‖L z‖ ^ 2

theorem projectedQuadratic_smooth (L : E →L[ℝ] F) (a c : ℝ) :
    ContDiff ℝ ∞ (projectedQuadratic L a c) := by
  exact contDiff_const.add (contDiff_const.mul (L.contDiff.norm_sq (𝕜 := ℝ)))

theorem fderiv_projectedQuadratic (L : E →L[ℝ] F) (a c : ℝ) (z : E) :
    fderiv ℝ (projectedQuadratic L a c) z =
      (2 * c) • (innerSL ℝ (L z)).comp L := by
  have h := ((hasFDerivAt_const a z).add
    ((L.hasFDerivAt.norm_sq).const_mul c)).fderiv
  change fderiv ℝ (projectedQuadratic L a c) z = _ at h
  rw [h]
  ext w
  simp only [zero_add, smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  ring

theorem hessian_projectedQuadratic (L : E →L[ℝ] F) (a c : ℝ) (z v w : E) :
    fderiv ℝ (fderiv ℝ (projectedQuadratic L a c)) z v w =
      2 * c * inner ℝ (L v) (L w) := by
  have he : fderiv ℝ (projectedQuadratic L a c) =
      fun y => (2 * c) • (innerSL ℝ (L y)).comp L := by
    funext y
    exact fderiv_projectedQuadratic L a c y
  rw [he]
  have h := (((innerSL ℝ).hasFDerivAt.comp z L.hasFDerivAt).clm_comp
    (hasFDerivAt_const L z)).const_smul (2 * c)
  have hh := h.fderiv
  simp only [Function.comp_def, Pi.smul_def] at hh
  rw [hh]
  simp
  left
  rfl

theorem hessian_log_ratio {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) {z : E} (hfz : f z ≠ 0) (hgz : g z ≠ 0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (f y / g y))) z v w =
      ((f z)⁻¹ * fderiv ℝ (fderiv ℝ f) z v w -
        (f z ^ 2)⁻¹ * fderiv ℝ f z v * fderiv ℝ f z w) -
      ((g z)⁻¹ * fderiv ℝ (fderiv ℝ g) z v w -
        (g z ^ 2)⁻¹ * fderiv ℝ g z v * fderiv ℝ g z w) := by
  have he : (fun y => Real.log (f y / g y)) =ᶠ[𝓝 z]
      fun y => Real.log (f y) - Real.log (g y) := by
    filter_upwards [hf.continuous.continuousAt.eventually_ne hfz,
      hg.continuous.continuousAt.eventually_ne hgz] with y hfy hgy
    exact Real.log_div hfy hgy
  rw [he.fderiv.fderiv_eq,
    hessian_sub_at (hf.contDiffAt.log hfz) (hg.contDiffAt.log hgz),
    hessian_log hf hfz, hessian_log hg hgz]

/-- The full real Hessian of the actual logarithmic test. -/
theorem thinProfile_hessian {m : ℕ} {η : ℝ} (hη : 0 < η) {z : ThinSpace m}
    (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) (v w : ThinSpace m) :
    fderiv ℝ (fderiv ℝ (thinProfile η)) z v w =
      2 / thinNumerator η z * inner ℝ v.2 w.2 -
      4 / thinNumerator η z ^ 2 * inner ℝ z.2 v.2 * inner ℝ z.2 w.2 +
      2 / thinDenominator η z * inner ℝ v.1 w.1 +
      4 / thinDenominator η z ^ 2 * inner ℝ z.1 v.1 * inner ℝ z.1 w.1 := by
  let Lp : ThinSpace m →L[ℝ] ThinTransverseSpace m := ContinuousLinearMap.snd ℝ _ _
  let Lx : ThinSpace m →L[ℝ] Space m := ContinuousLinearMap.fst ℝ _ _
  have hb : thinNumerator η = projectedQuadratic Lp (η ^ 2) 1 := by
    funext y
    simp [thinNumerator, projectedQuadratic, Lp]
  have hd : thinDenominator η = projectedQuadratic Lx (η ^ 2 + 1) (-1) := by
    funext y
    simp [thinDenominator, projectedQuadratic, Lx, sub_eq_add_neg]
  have hbs : ContDiff ℝ 2 (thinNumerator η : ThinSpace m → ℝ) := by
    rw [hb]
    exact (projectedQuadratic_smooth Lp _ _).of_le (by norm_num)
  have hds : ContDiff ℝ 2 (thinDenominator η : ThinSpace m → ℝ) := by
    rw [hd]
    exact (projectedQuadratic_smooth Lx _ _).of_le (by norm_num)
  unfold thinProfile
  rw [hessian_log_ratio hbs hds (thinNumerator_pos hη z).ne'
    (thinDenominator_pos hη hz).ne', hb, hd,
    hessian_projectedQuadratic, hessian_projectedQuadratic,
    fderiv_projectedQuadratic, fderiv_projectedQuadratic]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  dsimp [Lp, Lx]
  ring

end KakeyaSharp
