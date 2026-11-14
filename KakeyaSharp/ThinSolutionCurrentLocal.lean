/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinSolutionCurrent
public import KakeyaSharp.ThinParameterLocal
public import KakeyaSharp.ThinCurrentLocal

@[expose] public section

/-! The current energy estimate with local Dirichlet and conservation laws. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Calculus KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

theorem thinSolution_current_law_on {m : ℕ} {R : ℝ} (o : ThinSpace m)
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω)
    {U : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U)
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hH : ∀ y ∈ Ω ×ˢ thinBallAt R o, (A y).IsHermitian)
    (hd : RealColumnConservationOn (Ω ×ˢ thinBallAt R o) A)
    (hEq : ∀ p ∈ Ω, ∀ z, z ∈ thinBallAt R o →
      mooreDet m (thinQuaternionHessian (thinSlice U p) z) = currentDensity A (p,z))
    (p : Space 3) (hp : p ∈ Ω) (a : Fin 3) (z : ThinSpace m) (hz : z ∈ thinBallAt R o) :
    mooreDifferential m (thinQuaternionHessian (thinSlice U p) z)
      (thinQuaternionHessian (thinParameterDerivative U a p) z) +
      ∑ q, fderiv ℝ (thinVectorFlux (fun x => currentFlux A (p,x)) a q) z
        (thinDirection q.1 q.2) = 0 := by
  rw [thinSolution_linearized_on o hΩ hU (currentDensity_contDiff hA) hEq p hp z hz a]
  have he (q : Fin m × Fin 3) :
      fderiv ℝ (thinVectorFlux (fun x => currentFlux A (p,x)) a q) z (thinDirection q.1 q.2) =
        fderiv ℝ (currentRealFlux A a q) (p,z) (spatialDirection q) := by
    change fderiv ℝ (fun x => currentRealFlux A a q (p,x)) z (thinDirection q.1 q.2) = _
    apply fderiv_slice_right
    exact ((realCoefficientCLM threeSlots (q.1.succ,q.2) (0,a)).contDiff.comp hA).differentiable
      (by norm_num) (p,z)
  simp_rw [he]
  exact current_mass_conservation_on (hΩ.prod (thinBallAt_isOpen R o)) hH hd (p,z) ⟨hp,hz⟩ a

theorem thinSolution_current_energy_on {m N : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {Ω : Set (Space 3)} (hΩ : IsOpen Ω)
    {U : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U)
    (hb : ∀ p ∈ Ω, ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0)
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hH : ∀ y ∈ Ω ×ˢ thinBallAt R o, (A y).IsHermitian)
    (hd : RealColumnConservationOn (Ω ×ˢ thinBallAt R o) A)
    (hEq : ∀ p ∈ Ω, ∀ z, z ∈ thinBallAt R o →
      mooreDet m (thinQuaternionHessian (thinSlice U p) z) = currentDensity A (p,z))
    (p : Space 3) (hp : p ∈ Ω)
    (hpos : ∀ z ∈ thinBallAt R o, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian (thinSlice U p) z) w)
    (ρ : ThinSpace m → Fin N → ℝ) (b : ThinSpace m → Fin N → Fin m → Quaternion ℝ)
    (hρ : ∀ z ∈ thinBallAt R o, ∀ l, 0 ≤ ρ z l)
    (hmass : ∀ z ∈ thinBallAt R o, currentDensity A (p,z) = ∑ l, ρ z l)
    (hflux : ∀ z ∈ thinBallAt R o, currentFlux A (p,z) = ∑ l, ρ z l • b z l)
    (hstress : ∀ z ∈ thinBallAt R o, currentStress A (p,z) = ∑ l, ρ z l • outer (b z l)) :
    (∑ a, ∫ z in thinBallAt R o,
      quaternionForm (thinCofactor (thinSlice U p) z)
        (thinQuaternionGradient (thinParameterDerivative U a p) z)) ≤
      ∫ z in thinBallAt R o, realTrace (currentStress A (p,z) * thinQuaternionHessian (thinSlice U p) z) := by
  apply thinCurrent_energy_le_stress hR o (thinSlice_contDiff hU p) hpos
    (fun a => thinParameterDerivative U a p) (fun a => thinParameterDerivative_contDiff hU a p)
    (fun a z hz => thinParameterDerivative_boundary_on o hΩ (hU.of_le (by norm_num)) hb p hp a z hz)
    (fun z => currentFlux A (p,z))
    ((currentFlux_contDiff hA).comp (contDiff_const.prodMk contDiff_id))
    (fun z => currentStress A (p,z))
    ((currentStress_contDiff hA).continuous.comp (continuous_const.prodMk continuous_id))
    ρ b hρ (fun z hz => (hEq p hp z hz).trans (hmass z hz)) hflux hstress
  exact fun a z hz => thinSolution_current_law_on o hΩ hU hA hH hd hEq p hp a z hz


end KakeyaSharp
