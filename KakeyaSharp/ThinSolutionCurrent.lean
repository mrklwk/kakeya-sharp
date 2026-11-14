/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations, with Lean 4.35/mathlib API compatibility edits.
See MODULE_MIGRATION.json and provenance/lean435-port.json for the changes. -/
module

public import KakeyaSharp.ThinParameterHessian
public import KakeyaSharp.ThinCurrentEnergy

@[expose] public section

/-! The current estimate for actual parameter derivatives of a smooth
Dirichlet solution family. The linearized equation and differentiated boundary
condition are consequences here, not additional hypotheses. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Calculus KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

def currentFlux {m : ℕ}
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    (y : ThinCurrentSpace m) (i : Fin m) : Quaternion ℝ := A y i.succ 0

def currentStress {m : ℕ}
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    (y : ThinCurrentSpace m) : Matrix (Fin m) (Fin m) (Quaternion ℝ) :=
  fun i j => A y i.succ j.succ

theorem currentDensity_contDiff {m : ℕ} {n : ℕ∞ω}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ n A) : ContDiff ℝ n (currentDensity A) := by
  have h := (realCoefficientCLM threeSlots (0,0) (0,0)).contDiff.comp hA
  change ContDiff ℝ n (fun y => realCoefficients threeSlots (A y) (0,0) (0,0)) at h
  simpa only [realCoefficients, threeSlots, Matrix.cons_val_zero, star_one, one_mul,
    mul_one, currentDensity] using! h

theorem currentFlux_contDiff {m : ℕ} {n : ℕ∞ω}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ n A) : ContDiff ℝ n (currentFlux A) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_apply_apply ℝ (E := Quaternion ℝ) i.succ 0).comp hA

theorem currentStress_contDiff {m : ℕ} {n : ℕ∞ω}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ n A) : ContDiff ℝ n (currentStress A) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_apply_apply ℝ (E := Quaternion ℝ) i.succ j.succ).comp hA

theorem thinSolution_current_law {m : ℕ} {R : ℝ} (o : ThinSpace m)
    {U : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U)
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hH : ∀ y, (A y).IsHermitian) (hd : RealColumnConservation A)
    (hEq : ∀ p z, z ∈ thinBallAt R o →
      mooreDet m (thinQuaternionHessian (thinSlice U p) z) = currentDensity A (p,z))
    (p : Space 3) (a : Fin 3) (z : ThinSpace m) (hz : z ∈ thinBallAt R o) :
    mooreDifferential m (thinQuaternionHessian (thinSlice U p) z)
      (thinQuaternionHessian (thinParameterDerivative U a p) z) +
      ∑ q, fderiv ℝ (thinVectorFlux (fun x => currentFlux A (p,x)) a q) z
        (thinDirection q.1 q.2) = 0 := by
  rw [thinSolution_linearized o hU (currentDensity_contDiff hA) hEq p z hz a]
  have he (q : Fin m × Fin 3) :
      fderiv ℝ (thinVectorFlux (fun x => currentFlux A (p,x)) a q) z (thinDirection q.1 q.2) =
        fderiv ℝ (currentRealFlux A a q) (p,z) (spatialDirection q) := by
    change fderiv ℝ (fun x => currentRealFlux A a q (p,x)) z (thinDirection q.1 q.2) = _
    apply fderiv_slice_right
    exact ((realCoefficientCLM threeSlots (q.1.succ,q.2) (0,a)).contDiff.comp hA).differentiable
      (by norm_num) (p,z)
  simp_rw [he]
  exact current_mass_conservation hH hd (p,z) a

theorem thinSolution_current_energy {m N : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {U : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U)
    (hb : ∀ p z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0)
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hH : ∀ y, (A y).IsHermitian) (hd : RealColumnConservation A)
    (hEq : ∀ p z, z ∈ thinBallAt R o →
      mooreDet m (thinQuaternionHessian (thinSlice U p) z) = currentDensity A (p,z))
    (p : Space 3)
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
    (fun a z hz => thinParameterDerivative_boundary o (hU.of_le (by norm_num)) hb p a z hz)
    (fun z => currentFlux A (p,z))
    ((currentFlux_contDiff hA).comp (contDiff_const.prodMk contDiff_id))
    (fun z => currentStress A (p,z))
    ((currentStress_contDiff hA).continuous.comp (continuous_const.prodMk continuous_id))
    ρ b hρ (fun z hz => (hEq p z hz).trans (hmass z hz)) hflux hstress
  exact fun a z hz => thinSolution_current_law o hU hA hH hd hEq p a z hz

end KakeyaSharp
