/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinCurrentWeakLimit
public import KakeyaSharp.ThinValueSmoothLocal

@[expose] public section

/-! Positive source regularization and the weak limit with local equations.
No equation is required outside the open parameter domain. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set Filter KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem regularizedCurrent_isHermitian_at {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {y : ThinCurrentSpace m} (hA : (A y).IsHermitian) (ε : ℝ) :
    (regularizedCurrent A ε y).IsHermitian := by
  apply hA.add
  rw [Matrix.IsHermitian, quaternionMatrix_conjTranspose_real_smul,
    (outer_isHermitian (currentDensityUnit m)).eq]

theorem regularizedCurrent_conservation_on {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {D : Set (ThinCurrentSpace m)} (hd : RealColumnConservationOn D A) (ε : ℝ) :
    RealColumnConservationOn D (regularizedCurrent A ε) := by
  intro y hy q
  have he (p : Fin (m+1) × Fin 3) :
      (fun x => realCoefficients threeSlots (regularizedCurrent A ε x) p q) =
      (fun x => realCoefficients threeSlots (A x) p q +
        realCoefficients threeSlots (ε • outer (currentDensityUnit m)) p q) := by
    funext x
    exact (realCoefficientCLM threeSlots p q).map_add _ _
  simp_rw [he, fderiv_add_const]
  exact hd y hy q


theorem thinValueRealAt_current_weakSuperharmonic_of_regularized_solutions_on
    {m N : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R) (o : ThinSpace m) (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 2 A) (hH : ∀ y ∈ Ω ×ˢ thinBallAt R o, (A y).IsHermitian)
    (hd : RealColumnConservationOn (Ω ×ˢ thinBallAt R o) A)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hεb : ∀ n, ε n ∈ Ioc (0 : ℝ) 1)
    (U : ℕ → ThinCurrentSpace m → ℝ) (hU : ∀ n, ContDiff ℝ 3 (U n))
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
  apply thinValueRealAt_weakSuperharmonic_regularization hm hR o Ω hΩ
    (currentDensity_contDiff hA).continuous hε (fun n => ⟨(hεb n).1.le,(hεb n).2⟩)
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
  have h := thinValueRealAt_current_weakSuperharmonic_on hR o Ω hΩ (hU n) (hadm n)
    (regularizedCurrent_contDiff hA (ε n)) (fun y hy => regularizedCurrent_isHermitian_at (hH y hy) (ε n))
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
