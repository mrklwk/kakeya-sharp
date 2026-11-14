/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.CoordinateDerivative

@[expose] public section

/-! Identification of the algebraic phase gradient with actual Frechet
derivatives. In particular, tangency holds for the physical packet. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp.Packet
open KakeyaSharp.QuaternionAlgebra

def parameterGradientAt {m : ℕ} (r : ℝ) (a v : Fin m → ℝ)
    (y : ThinCurrentSpace m) (j : Fin m) : Q :=
  parameterPhaseGradient (y.1 1/radius y) (y.1 2/radius y)
    (ratioRe y j) (ratioIm y j) (centers r a v y j) (residuals r a v y j)

def spatialGradientAt {m : ℕ} (r : ℝ) (a v : Fin m → ℝ)
    (y : ThinCurrentSpace m) (j : Fin m) : Q :=
  spatialPhaseGradient (y.1 1/radius y) (y.1 2/radius y)
    (ratioRe y j) (ratioIm y j) (centers r a v y j) (residuals r a v y j)

def scalarPhysicalRate {m : ℕ} (r : ℝ) (a v : Fin m → ℝ)
    (y z : ThinCurrentSpace m) (j : Fin m) : ℝ :=
  (parameterGradientAt r a v y j).re*z.1 0+
  (parameterGradientAt r a v y j).imI*z.1 1+
  (parameterGradientAt r a v y j).imJ*z.1 2+
  (spatialGradientAt r a v y j).re*z.2.1 j+
  (spatialGradientAt r a v y j).imI*z.2.2 (j,0)+
  (spatialGradientAt r a v y j).imJ*z.2.2 (j,1)

theorem hasDerivAt_scalarPhysicalPhase_line {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (z : ThinCurrentSpace m) (j : Fin m) :
    HasDerivAt (fun t => scalarPhase r (radius (line y z t)) (time (line y z t))
      (a j) (v j) ((line y z t).2.1 j) (ratioRe (line y z t) j) (ratioIm (line y z t) j))
      (scalarPhysicalRate r a v y z j) 0 := by
  have he : line y z 0=y := by simp [line]
  have h := hasDerivAt_scalarPhase_curve (a := a j) (v := v j) hr
    (hasDerivAt_radius_line hy z) (hasDerivAt_time_line y z)
    (hasDerivAt_line_x y z j) (hasDerivAt_ratioRe_line hy z j) (hasDerivAt_ratioIm_line hy z j)
    (congrArg radius he) (congrArg time he) (congrArg (fun w => w.2.1 j) he)
    (congrArg (fun w => ratioRe w j) he) (congrArg (fun w => ratioIm w j) he) hy
  refine h.congr_deriv ?_
  dsimp only [scalarPhysicalRate, parameterGradientAt, spatialGradientAt,
    parameterPhaseGradient, spatialPhaseGradient, centers, residuals,
    realRate, imaginaryRate, radialRate, angularRate]
  have hs := hy.ne'
  field_simp
  ring

theorem physicalPhase_fderiv {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (z : ThinCurrentSpace m) :
    fderiv ℝ (physicalPhase r a v) y z = ∑ j, scalarPhysicalRate r a v y z j := by
  apply fderiv_eq_of_line ((physicalPhase_contDiffAt (n := 1) hr a v hy).differentiableAt (by norm_num))
  convert HasDerivAt.sum (u := Finset.univ) (fun j _ => hasDerivAt_scalarPhysicalPhase_line hr a v hy z j) using 1
  funext t
  simp only [physicalPhase, phase, Finset.sum_apply]

private theorem sum_components {ι : Type*} (s : Finset ι) (f : ι → Q) :
    (∑ j ∈ s, f j) = ⟨∑ j ∈ s, (f j).re, ∑ j ∈ s, (f j).imI,
      ∑ j ∈ s, (f j).imJ, ∑ j ∈ s, (f j).imK⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert j s hj ih => simp only [Finset.sum_insert hj, ih]; rfl

theorem physicalPhase_gradient {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    gradientMap threeSlots (fun p => fderiv ℝ (physicalPhase r a v) y (currentDirection p)) =
      phaseGradient (y.1 1/radius y) (y.1 2/radius y)
        (ratioRe y) (ratioIm y) (centers r a v y) (residuals r a v y) := by
  classical
  funext j
  rw [gradientMap_threeSlots]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [phaseGradient, Fin.cases_zero]
    rw [sum_components]
    ext <;> simp [physicalPhase_fderiv hr a v hy, scalarPhysicalRate,
      currentDirection, parameterDirection, parameterGradientAt, parameterPhaseGradient]
  · ext <;> simp [physicalPhase_fderiv hr a v hy, scalarPhysicalRate,
      currentDirection, spatialDirection, thinDirection, phaseGradient, spatialGradientAt,
      spatialPhaseGradient]

theorem physicalColumn_tangency {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    (∑ j, star (physicalColumn r a v y j)*
      gradientMap threeSlots (fun p => fderiv ℝ (physicalPhase r a v) y (currentDirection p)) j) = 0 := by
  rw [physicalPhase_gradient hr a v hy]
  exact physicalColumn_tangency_formula r a v hy

end KakeyaSharp.Packet
