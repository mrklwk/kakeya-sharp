/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.CompactParameterIntegral
public import KakeyaSharp.ThinCurrentCurvature
public import KakeyaSharp.Green.DistributionalLaplacian

@[expose] public section

/-! Joint C2 regularity of the represented variational value and the weak
Laplacian inequality for actual smooth solution families. -/
noncomputable section
namespace KakeyaSharp
open Set MeasureTheory InnerProductSpace Laplacian KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

theorem thinValueRealAt_contDiff_two_of_solution {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 2 U) (hρ : ContDiff ℝ 2 ρ)
    (hadm : ∀ p, ThinAdmissibleAt R o (thinSlice U p))
    (hEq : ∀ p z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z)) :
    ContDiff ℝ 2 (fun p => thinValueRealAt R o (thinSlice ρ p)) := by
  have he : (fun p => thinValueRealAt R o (thinSlice ρ p)) =
      (fun p => (m : ℝ)/((m : ℝ)+1) * ∫ z in thinBallAt R o, (-U (p,z))*ρ (p,z)) := by
    funext p
    exact thinValueRealAt_PDE_representation hR
      (thinSlice_contDiff hρ p).continuous.continuousOn (hadm p) (hEq p)
  rw [he]
  exact contDiff_const.mul (contDiff_two_setIntegral_compact (μ := volume)
    (thinBallAt_measurable R o) (thinClosedBallAt_compact hR.le o)
    (fun z hz => show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le) (hU.neg.mul hρ))

theorem thinValueRealAt_current_weakSuperharmonic {m N : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) (Ω : Set (Space 3))
    {U : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U)
    (hadm : ∀ p, ThinAdmissibleAt R o (thinSlice U p))
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 2 A) (hH : ∀ y, (A y).IsHermitian) (hd : RealColumnConservation A)
    (hEq : ∀ p z, z ∈ thinBallAt R o →
      mooreDet m (thinQuaternionHessian (thinSlice U p) z) = currentDensity A (p,z))
    (hpos : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian (thinSlice U p) z) w)
    (hzS : ∀ p ∈ Ω, ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → currentStress A (p,z) = 0)
    (ρ : ThinCurrentSpace m → Fin N → ℝ) (b : ThinCurrentSpace m → Fin N → Fin m → Quaternion ℝ)
    (hρ : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, ∀ l, 0 ≤ ρ (p,z) l)
    (hmass : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, currentDensity A (p,z) = ∑ l, ρ (p,z) l)
    (hflux : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, currentFlux A (p,z) = ∑ l, ρ (p,z) l • b (p,z) l)
    (hstress : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o,
      currentStress A (p,z) = ∑ l, ρ (p,z) l • QuaternionAlgebra.outer (b (p,z) l)) :
    WeakSuperharmonicOn Ω (fun p => thinValueRealAt R o (thinSlice (currentDensity A) p)) := by
  have hF := thinValueRealAt_contDiff_two_of_solution hR o (hU.of_le (by norm_num))
    (currentDensity_contDiff hA) hadm hEq
  apply weakSuperharmonicOn_of_laplacian_nonpos hF
  intro p hp
  have h := thinValueRealAt_current_laplacian_nonpos hR o hU hadm hA hH hd hEq p
    (hpos p hp) (hzS p hp) (fun z => ρ (p,z)) (fun z => b (p,z)) (hρ p hp)
    (hmass p hp) (hflux p hp) (hstress p hp)
  simpa only [parameterLine, secondDeriv_line hF, ← laplacian_space_eq_sum] using h

end KakeyaSharp
