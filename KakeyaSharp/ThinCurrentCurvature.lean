/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinSolutionCurrent
public import KakeyaSharp.ThinValueCurvature
public import KakeyaSharp.Green.DoubleDivergence

@[expose] public section

/-! The nonpositive sum of actual second parameter derivatives of the
variational supremum. Existence of a smooth Dirichlet family is explicit.
The spatial stress is assumed to vanish on the boundary of the fixed ball. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open KakeyaSharp.Calculus KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

theorem thinCurrent_stress_transfer {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 2 A) (hH : ∀ y, (A y).IsHermitian) (hd : RealColumnConservation A)
    (p : Space 3) {u : ThinSpace m → ℝ} (hu : ContDiff ℝ 2 u)
    (hzu : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → u z = 0)
    (hzS : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → currentStress A (p,z) = 0) :
    (∫ z in thinBallAt R o, u z * (∑ a, fderiv ℝ (fderiv ℝ (currentDensity A)) (p,z)
      (parameterDirection a) (parameterDirection a))) =
      ∫ z in thinBallAt R o, realTrace (currentStress A (p,z) * thinQuaternionHessian u z) := by
  let : (volume : Measure (ThinSpace m)).IsAddHaarMeasure := by
    change ((volume : Measure (Space m)).prod (volume : Measure (ThinTransverseSpace m))).IsAddHaarMeasure
    infer_instance
  let K : (Fin m × Fin 3) → (Fin m × Fin 3) → ThinSpace m → ℝ :=
    fun i j z => currentRealStress A j i (p,z)
  have hKjoint (i j : Fin m × Fin 3) : ContDiff ℝ 2 (currentRealStress A j i) :=
    (realCoefficientCLM threeSlots (j.1.succ,j.2) (i.1.succ,i.2)).contDiff.comp hA
  have hK (i j : Fin m × Fin 3) : ContDiff ℝ 2 (K i j) :=
    (hKjoint i j).comp (contDiff_const.prodMk contDiff_id)
  have hzK (i j : Fin m × Fin 3) (z : ThinSpace m) (hz : z ∈ frontier (thinBallAt R o)) : K i j z = 0 := by
    change (star (threeSlots j.2) * currentStress A (p,z) j.1 i.1 * threeSlots i.2).re = 0
    rw [hzS z (thinBallAt_frontier_subset R o hz)]
    simp
  have hT := integral_double_divergence_transfer (μ := volume)
    (thinBallAt_isOpen R o) (thinBallAt_bounded hR.le o) (thinBallAt_null_frontier R o) hu
    (fun z hz => hzu z (thinBallAt_frontier_subset R o hz))
    (fun i : Fin m × Fin 3 => thinDirection i.1 i.2) K hK hzK
  refine Eq.trans ?_ (hT.trans ?_)
  · apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z _
    dsimp only
    rw [current_double_conservation hA hH hd (p,z)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (secondDerivative_slice_right (hKjoint i j) p z
      (thinDirection i.1 i.2) (thinDirection j.1 j.2)).symm
  · apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z _
    dsimp only
    rw [Finset.sum_comm]
    change (∑ i, ∑ j, realCoefficients threeSlots (currentStress A (p,z)) i j * thinRealHessian u z i j) = _
    exact (realTrace_hessianMap (currentStress A (p,z)) threeSlots (thinRealHessian u z)
      (directionalRealHessian_isSymm (fun i => thinDirection i.1 i.2) hu.contDiffAt)).symm

theorem thinValueRealAt_current_laplacian_nonpos {m N : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {U : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U)
    (hadm : ∀ p, ThinAdmissibleAt R o (thinSlice U p))
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 2 A) (hH : ∀ y, (A y).IsHermitian) (hd : RealColumnConservation A)
    (hEq : ∀ p z, z ∈ thinBallAt R o →
      mooreDet m (thinQuaternionHessian (thinSlice U p) z) = currentDensity A (p,z))
    (p : Space 3)
    (hpos : ∀ z ∈ thinBallAt R o, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian (thinSlice U p) z) w)
    (hzS : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → currentStress A (p,z) = 0)
    (ρ : ThinSpace m → Fin N → ℝ) (b : ThinSpace m → Fin N → Fin m → Quaternion ℝ)
    (hρ : ∀ z ∈ thinBallAt R o, ∀ l, 0 ≤ ρ z l)
    (hmass : ∀ z ∈ thinBallAt R o, currentDensity A (p,z) = ∑ l, ρ z l)
    (hflux : ∀ z ∈ thinBallAt R o, currentFlux A (p,z) = ∑ l, ρ z l • b z l)
    (hstress : ∀ z ∈ thinBallAt R o, currentStress A (p,z) = ∑ l, ρ z l • outer (b z l)) :
    (∑ a : Fin 3, deriv (deriv (fun t =>
      thinValueRealAt R o (thinSlice (currentDensity A) (parameterLine p a t)))) 0) ≤ 0 := by
  have hb : ∀ p z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0 :=
    fun p => (hadm p).2.1
  have hρ2 := currentDensity_contDiff hA
  have hi (a : Fin 3) : IntegrableOn (fun z => U (p,z) *
      fderiv ℝ (fderiv ℝ (currentDensity A)) (p,z) (parameterDirection a) (parameterDirection a))
      (thinBallAt R o) := continuous_integrableOn_thinBallAt hR o
        ((thinSlice_contDiff hU p).continuous.mul
          ((continuous_second_directional hρ2 _ _).comp (continuous_const.prodMk continuous_id)))
  have hstressIntegral : (∑ a : Fin 3, ∫ z in thinBallAt R o, U (p,z) *
      fderiv ℝ (fderiv ℝ (currentDensity A)) (p,z) (parameterDirection a) (parameterDirection a)) =
      ∫ z in thinBallAt R o, realTrace (currentStress A (p,z) * thinQuaternionHessian (thinSlice U p) z) := by
    rw [← integral_finsetSum _ (fun a _ => hi a)]
    simp_rw [← Finset.mul_sum]
    exact thinCurrent_stress_transfer hR o hA hH hd p
      (thinSlice_contDiff (hU.of_le (by norm_num)) p) (hb p) hzS
  simp_rw [thinValueRealAt_parameter_curvature hR o hU hρ2 hadm hEq p]
  rw [Finset.sum_sub_distrib, hstressIntegral]
  exact sub_nonpos.mpr (thinSolution_current_energy hR o hU hb (hA.of_le (by norm_num))
    hH hd hEq p hpos ρ b hρ hmass hflux hstress)

end KakeyaSharp
