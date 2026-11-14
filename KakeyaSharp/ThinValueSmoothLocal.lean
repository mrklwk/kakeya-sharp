/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinCurrentCurvatureLocal
public import KakeyaSharp.ThinValueSmooth
public import KakeyaSharp.Green.LocalLaplacian

@[expose] public section

/-! Distributional superharmonicity from equations on an open parameter
region. Global smooth representatives do not have to satisfy equations outside it. -/
noncomputable section
namespace KakeyaSharp
open Set MeasureTheory InnerProductSpace Laplacian KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

theorem thinValueRealAt_contDiffOn_two_of_solution {m : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) (Ω : Set (Space 3))
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 2 U) (hρ : ContDiff ℝ 2 ρ)
    (hadm : ∀ p ∈ Ω, ThinAdmissibleAt R o (thinSlice U p))
    (hEq : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o,
      mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z)) :
    ContDiffOn ℝ 2 (fun p => thinValueRealAt R o (thinSlice ρ p)) Ω := by
  have hF : ContDiff ℝ 2 (fun p => (m : ℝ)/((m : ℝ)+1) *
      ∫ z in thinBallAt R o, (-U (p,z))*ρ (p,z)) :=
    contDiff_const.mul (contDiff_two_setIntegral_compact (μ := volume)
      (thinBallAt_measurable R o) (thinClosedBallAt_compact hR.le o)
      (fun z hz => show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le) (hU.neg.mul hρ))
  apply hF.contDiffOn.congr
  intro p hp
  exact thinValueRealAt_PDE_representation hR
    (thinSlice_contDiff hρ p).continuous.continuousOn (hadm p hp) (hEq p hp)

theorem thinValueRealAt_current_weakSuperharmonic_on {m N : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    {U : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U)
    (hadm : ∀ p ∈ Ω, ThinAdmissibleAt R o (thinSlice U p))
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 2 A) (hH : ∀ y ∈ Ω ×ˢ thinBallAt R o, (A y).IsHermitian)
    (hd : RealColumnConservationOn (Ω ×ˢ thinBallAt R o) A)
    (hEq : ∀ p ∈ Ω, ∀ z, z ∈ thinBallAt R o →
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
  have hF := thinValueRealAt_contDiffOn_two_of_solution hR o Ω (hU.of_le (by norm_num))
    (currentDensity_contDiff hA) hadm hEq
  apply weakSuperharmonicOn_of_contDiffOn_laplacian_nonpos hΩ hF
  intro p hp
  have h := thinValueRealAt_current_laplacian_nonpos_on hR o hΩ hU hadm hA hH hd hEq p hp
    (hpos p hp) (hzS p hp) (fun z => ρ (p,z)) (fun z => b (p,z)) (hρ p hp)
    (hmass p hp) (hflux p hp) (hstress p hp)
  simpa only [parameterLine, secondDeriv_line_of_contDiffAt ((hF p hp).contDiffAt (hΩ.mem_nhds hp)), ← laplacian_space_eq_sum] using h


end KakeyaSharp
