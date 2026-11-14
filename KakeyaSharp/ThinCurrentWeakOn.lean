/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinCurrentWeakLimitLocal
public import KakeyaSharp.ThinValueSmoothOn
public import KakeyaSharp.ThinValueLocalWeakLimit

@[expose] public section

/-! The weak scalar transfer theorem on the actual local parameter domain,
with no global smoothness, no global conservation, and no limiting Dirichlet
solution hypothesis. Existence of the regularized local solution families is
still an explicit assumption. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set Filter KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem currentDensity_contDiffAt {m : ℕ} {n : ℕ∞ω}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {y : ThinCurrentSpace m} (hA : ContDiffAt ℝ n A y) : ContDiffAt ℝ n (currentDensity A) y := by
  have h := (realCoefficientCLM threeSlots (0,0) (0,0)).contDiff.contDiffAt.comp y hA
  change ContDiffAt ℝ n (fun z => realCoefficients threeSlots (A z) (0,0) (0,0)) y at h
  simpa only [realCoefficients, threeSlots, Matrix.cons_val_zero, star_one, one_mul,
    mul_one, currentDensity] using! h

theorem regularizedCurrent_contDiffAt {m : ℕ} {n : ℕ∞ω}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {y : ThinCurrentSpace m} (hA : ContDiffAt ℝ n A y) (ε : ℝ) :
    ContDiffAt ℝ n (regularizedCurrent A ε) y := hA.add contDiffAt_const

theorem thinValueRealAt_current_weakSuperharmonic_of_local_regularized_solutions
    {m N : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R) (o : ThinSpace m) (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ∀ p ∈ Ω, ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 2 A (p,z)) (hH : ∀ y ∈ Ω ×ˢ thinBallAt R o, (A y).IsHermitian)
    (hd : RealColumnConservationOn (Ω ×ˢ thinBallAt R o) A)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hεb : ∀ n, ε n ∈ Ioc (0 : ℝ) 1)
    (U : ℕ → ThinCurrentSpace m → ℝ) (hU : ∀ n p, p ∈ Ω → ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 3 (U n) (p,z))
    (hadm : ∀ n p, p ∈ Ω → ThinAdmissibleAt R o (thinSlice (U n) p))
    (hEq : ∀ n p, p ∈ Ω → ∀ z, z ∈ thinBallAt R o →
      mooreDet m (thinQuaternionHessian (thinSlice (U n) p) z) = currentDensity A (p,z)+ε n)
    (hpos : ∀ n p, p ∈ Ω → ∀ z ∈ thinBallAt R o, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian (thinSlice (U n) p) z) w)
    (hzS : ∀ p ∈ Ω, ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → currentStress A (p,z) = 0)
    (ρ : ThinCurrentSpace m → Fin N → ℝ) (b : ThinCurrentSpace m → Fin N → Fin m → Quaternion ℝ)
    (hρ : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, ∀ l, 0 ≤ ρ (p,z) l)
    (hmass : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, currentDensity A (p,z) = ∑ l, ρ (p,z) l)
    (hflux : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, currentFlux A (p,z) = ∑ l, ρ (p,z) l • b (p,z) l)
    (hstress : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o,
      currentStress A (p,z) = ∑ l, ρ (p,z) l • outer (b (p,z) l)) :
    WeakSuperharmonicOn Ω (fun p => thinValueRealAt R o (thinSlice (currentDensity A) p)) := by
  apply thinValueRealAt_weakSuperharmonic_regularization_on hm hR o Ω hΩ
    (fun y hy => (currentDensity_contDiffAt (hA y.1 hy.1 y.2 hy.2)).continuousAt.continuousWithinAt) hε (fun n => ⟨(hεb n).1.le,(hεb n).2⟩)
  intro n
  have hEn (p : Space 3) (hp : p ∈ Ω) (z : ThinSpace m) (hz : z ∈ thinBallAt R o) :
      mooreDet m (thinQuaternionHessian (thinSlice (U n) p) z) =
        currentDensity (regularizedCurrent A (ε n)) (p,z) := by
    rw [currentDensity_regularized]
    exact hEq n p hp z hz
  have hSn (p : Space 3) (hp : p ∈ Ω) (z : ThinSpace m)
      (hz : ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2) :
      currentStress (regularizedCurrent A (ε n)) (p,z) = 0 := by
    rw [currentStress_regularized]
    exact hzS p hp z hz
  have h := thinValueRealAt_current_weakSuperharmonic_of_local_smoothness hR o Ω hΩ (hU n) (hadm n)
    (fun p hp z hz => regularizedCurrent_contDiffAt (hA p hp z hz) (ε n)) (fun y hy => regularizedCurrent_isHermitian_at (hH y hy) (ε n))
    (regularizedCurrent_conservation_on hd (ε n)) hEn (hpos n) hSn
    (regularizedWeights ρ (ε n)) (regularizedDirections b)
    (fun p hp z hz => regularizedWeights_nonneg (hεb n).1.le (hρ p hp z hz))
    (fun p hp z hz => regularizedCurrent_mass (hmass p hp z hz) (ε n))
    (fun p hp z hz => regularizedCurrent_flux (hflux p hp z hz) (ε n))
    (fun p hp z hz => regularizedCurrent_stress (hstress p hp z hz) (ε n))
  have he : (fun p => thinValueRealAt R o (thinSlice (currentDensity (regularizedCurrent A (ε n))) p)) =
      (fun p => thinValueRealAt R o (fun z => currentDensity A (p,z)+ε n)) := by
    funext p
    congr 1
    funext z
    exact currentDensity_regularized A (ε n) (p,z)
  rwa [he] at h



end KakeyaSharp
