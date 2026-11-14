/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.DistributionalLaplacian
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MollificationDerivatives

@[expose] public section

/-! Positive smoothing of a weakly superharmonic function on an interior region. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Propagation
open MeasureTheory Set Metric Filter Laplacian
open OAI.Analysis.PDE.Schauder
open scoped ContDiff Topology Convolution

theorem second_fderiv_convolution_kernel {m : ℕ} (g κ : Space m → ℝ)
    (hg : Continuous g) (hκ : ContDiff ℝ 2 κ) (hs : HasCompactSupport κ)
    (x v w : Space m) :
    fderiv ℝ (fderiv ℝ (scalarConvolution g κ)) x v w =
      ∫ y, g y*fderiv ℝ (fderiv ℝ κ) (x-y) v w := by
  have hκ1 : ContDiff ℝ 1 κ := hκ.of_le (by norm_num)
  have hDκ : ContDiff ℝ 1 (fderiv ℝ κ) := hκ.fderiv_right (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ (scalarConvolution g κ)) :=
    (contDiff_scalarConvolution g κ hg.locallyIntegrable hκ hs).fderiv_right (by norm_num)
  have he : (fun z => fderiv ℝ (scalarConvolution g κ) z w) =
      scalarConvolution g (fun z => fderiv ℝ κ z w) :=
    funext (fun z => fderiv_scalarConvolution_data g κ hg.locallyIntegrable hκ1 hs z w)
  rw [← fderiv_apply_const _ x w v (hD.differentiable one_ne_zero x),he,
    fderiv_scalarConvolution_data g _ hg.locallyIntegrable
      (hDκ.clm_apply contDiff_const) (hs.fderiv_apply ℝ w)]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => congrArg (fun t => g y*t)
    (fderiv_apply_const _ (x-y) w v (hDκ.differentiable one_ne_zero _)))

theorem laplacian_convolution_kernel {m : ℕ} (g κ : Space m → ℝ)
    (hg : Continuous g) (hκ : ContDiff ℝ 2 κ) (hs : HasCompactSupport κ) (x : Space m) :
    Δ (scalarConvolution g κ) x = ∫ y, g y*Δ κ (x-y) := by
  simp_rw [Green.laplacian_space_eq_sum,second_fderiv_convolution_kernel g κ hg hκ hs,
    Finset.mul_sum]
  rw [integral_finsetSum]
  intro i _
  let v : Space m := EuclideanSpace.single i 1
  have hcont : Continuous (fun y => fderiv ℝ (fderiv ℝ κ) y v v) :=
    Green.continuous_second_directional hκ v v
  have hcomp : HasCompactSupport (fun y => fderiv ℝ (fderiv ℝ κ) y v v) := by
    have h := (hs.fderiv_apply ℝ v).fderiv_apply ℝ v
    simpa only [Green.directional_twice hκ] using h
  exact hcomp.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hg.locallyIntegrable hcont x

theorem laplacian_reflect_translate {m : ℕ} {κ : Space m → ℝ}
    (hκ : ContDiff ℝ 2 κ) (x y : Space m) :
    Δ (fun z => κ (x-z)) y = Δ κ (x-y) := by
  simp only [Green.laplacian_space_eq_sum,second_fderiv_reflect_translate κ hκ]

def mollified (φ : ContDiffBump (0 : Space 3)) (g : Space 3 → ℝ) : Space 3 → ℝ :=
  scalarConvolution g (φ.normed volume)

theorem mollified_smooth (φ : ContDiffBump (0 : Space 3)) {g : Space 3 → ℝ}
    (hg : Continuous g) : ContDiff ℝ ∞ (mollified φ g) :=
  contDiff_scalarConvolution g _ hg.locallyIntegrable φ.contDiff_normed φ.hasCompactSupport_normed

theorem translated_mollifier_support (φ : ContDiffBump (0 : Space 3)) (x : Space 3) :
    tsupport (fun y => φ.normed volume (x-y)) ⊆ closedBall x φ.rOut := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  have hs : x-y ∈ Function.support (φ.normed volume) := hy
  rw [φ.support_normed_eq] at hs
  have hn : ‖x-y‖ < φ.rOut := by simpa only [mem_ball,dist_zero_right] using hs
  simpa only [mem_closedBall,dist_eq_norm'] using hn.le

theorem mollified_laplacian_nonpos (φ : ContDiffBump (0 : Space 3))
    {Ω : Set (Space 3)} {f g : Space 3 → ℝ} (hg : Continuous g)
    (hw : Green.WeakSuperharmonicOn Ω f) (x : Space 3)
    (hΩ : closedBall x φ.rOut ⊆ Ω)
    (he : EqOn g f (closedBall x φ.rOut)) :
    Δ (mollified φ g) x ≤ 0 := by
  let ψ : Space 3 → ℝ := fun y => φ.normed volume (x-y)
  have hψ : ContDiff ℝ ∞ ψ := φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have hs : HasCompactSupport ψ := φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
  have hsub : tsupport ψ ⊆ closedBall x φ.rOut := translated_mollifier_support φ x
  have hweak := (hw.2 ψ hψ hs (hsub.trans hΩ) (fun _ => φ.nonneg_normed _)).2
  rw [mollified,laplacian_convolution_kernel g _ hg φ.contDiff_normed φ.hasCompactSupport_normed]
  have heq : (∫ y, g y*Δ (φ.normed volume) (x-y)) = ∫ y, f y*Δ ψ y := by
    apply integral_congr_ae
    apply ae_of_all
    intro y
    have hΔ : Δ ψ y=Δ (φ.normed volume) (x-y) :=
      laplacian_reflect_translate φ.contDiff_normed x y
    change g y*Δ (φ.normed volume) (x-y) = f y*Δ ψ y
    rw [← hΔ]
    by_cases hy : y ∈ tsupport ψ
    · rw [he (hsub hy)]
    · rw [Green.laplacian_eq_zero_off_tsupport hy]
      simp
  exact heq ▸ hweak

theorem mollified_nonneg (φ : ContDiffBump (0 : Space 3))
    {g : Space 3 → ℝ} (x : Space 3) (hn : ∀ y ∈ closedBall x φ.rOut, 0 ≤ g y) :
    0 ≤ mollified φ g x := by
  apply integral_nonneg
  intro y
  by_cases hy : φ.normed volume (x-y)=0
  · simp [hy]
  · have hys : y ∈ tsupport (fun y => φ.normed volume (x-y)) :=
      subset_closure (show y ∈ Function.support (fun y => φ.normed volume (x-y)) from hy)
    exact mul_nonneg (hn y (translated_mollifier_support φ x hys)) (φ.nonneg_normed _)

theorem mollified_tendsto {g : Space 3 → ℝ} (hg : Continuous g) (x : Space 3) :
    Tendsto (fun k => mollified (standardMollifier 3 k) g x) atTop (𝓝 (g x)) := by
  have he (φ : ContDiffBump (0 : Space 3)) : mollified φ g = smoothData φ g := by
    funext z
    unfold mollified smoothData scalarConvolution
    rw [← integral_sub_left_eq_self (fun y => g y*φ.normed volume (z-y)) volume z]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by simp [mul_comm])
  simp_rw [he]
  exact smoothData_tendsto g hg x

theorem mollified_norm_le (φ : ContDiffBump (0 : Space 3))
    {g : Space 3 → ℝ} {M : ℝ} (x : Space 3)
    (hb : ∀ y ∈ closedBall x φ.rOut, ‖g y‖ ≤ M) :
    ‖mollified φ g x‖ ≤ M := by
  have hc : Continuous (fun y => φ.normed volume (x-y)) :=
    φ.continuous_normed.comp (continuous_const.sub continuous_id)
  have hs : HasCompactSupport (fun y => φ.normed volume (x-y)) :=
    φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
  have h := norm_integral_le_of_norm_le (μ := volume) ((hc.integrable_of_hasCompactSupport hs).const_mul M)
    (ae_of_all _ (fun y => by
      change ‖g y*φ.normed volume (x-y)‖ ≤ M*φ.normed volume (x-y)
      rw [norm_mul,Real.norm_of_nonneg (φ.nonneg_normed _)]
      by_cases hy : φ.normed volume (x-y)=0
      · simp [hy]
      · have hys : y ∈ tsupport (fun y => φ.normed volume (x-y)) :=
          subset_closure (show y ∈ Function.support (fun y => φ.normed volume (x-y)) from hy)
        exact mul_le_mul_of_nonneg_right (hb y (translated_mollifier_support φ x hys))
          (φ.nonneg_normed _)))
  have he : (∫ y, φ.normed volume (x-y))=1 :=
    (integral_sub_left_eq_self (φ.normed volume) volume x).trans φ.integral_normed
  simpa only [mollified,scalarConvolution,integral_const_mul,he,mul_one] using h

end KakeyaSharp.Propagation
