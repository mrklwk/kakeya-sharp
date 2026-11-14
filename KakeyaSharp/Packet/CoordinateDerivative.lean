/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Smooth

@[expose] public section

/-! Derivatives in the physical coordinates, away from Y = 0. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp.Packet
open KakeyaSharp.QuaternionAlgebra

def line {E : Type*} [Add E] [SMul ℝ E] (y z : E) (t : ℝ) : E := y+t • z

theorem hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y z : E) : HasDerivAt (line y z) z 0 := by
  simpa only [line, id_eq, one_smul] using!
    ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add y

theorem fderiv_eq_of_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {y z : E} {v : F}
    (hf : DifferentiableAt ℝ f y) (h : HasDerivAt (fun t => f (line y z t)) v 0) :
    fderiv ℝ f y z = v := by
  have he : y = line y z 0 := by simp [line]
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line y z) he).unique h

theorem hasDerivAt_line_parameter {m : ℕ} (y z : ThinCurrentSpace m) (i : Fin 3) :
    HasDerivAt (fun t => (line y z t).1 i) (z.1 i) 0 := by
  simpa [line] using ((hasDerivAt_id (0 : ℝ)).mul_const (z.1 i)).const_add (y.1 i)

theorem hasDerivAt_line_x {m : ℕ} (y z : ThinCurrentSpace m) (j : Fin m) :
    HasDerivAt (fun t => (line y z t).2.1 j) (z.2.1 j) 0 := by
  simpa [line] using ((hasDerivAt_id (0 : ℝ)).mul_const (z.2.1 j)).const_add (y.2.1 j)

theorem hasDerivAt_line_p {m : ℕ} (y z : ThinCurrentSpace m) (j : Fin m × Fin 2) :
    HasDerivAt (fun t => (line y z t).2.2 j) (z.2.2 j) 0 := by
  simpa [line] using ((hasDerivAt_id (0 : ℝ)).mul_const (z.2.2 j)).const_add (y.2.2 j)

def radialRate {m : ℕ} (y z : ThinCurrentSpace m) : ℝ :=
  (y.1 1*z.1 1+y.1 2*z.1 2)/radius y

def angularRate {m : ℕ} (y z : ThinCurrentSpace m) : ℝ :=
  (-y.1 2*z.1 1+y.1 1*z.1 2)/radius y

def realRate {m : ℕ} (y z : ThinCurrentSpace m) (j : Fin m) : ℝ :=
  (y.1 1*z.2.2 (j,0)+y.1 2*z.2.2 (j,1))/(radius y)^2-
    (ratioRe y j*radialRate y z-ratioIm y j*angularRate y z)/radius y

def imaginaryRate {m : ℕ} (y z : ThinCurrentSpace m) (j : Fin m) : ℝ :=
  (-y.1 2*z.2.2 (j,0)+y.1 1*z.2.2 (j,1))/(radius y)^2-
    (ratioIm y j*radialRate y z+ratioRe y j*angularRate y z)/radius y

theorem hasDerivAt_radius_line {m : ℕ} {y : ThinCurrentSpace m}
    (hy : 0 < radius y) (z : ThinCurrentSpace m) :
    HasDerivAt (fun t => radius (line y z t)) (radialRate y z) 0 := by
  have hQ := ((hasDerivAt_line_parameter y z 1).pow 2).add
    ((hasDerivAt_line_parameter y z 2).pow 2)
  have hne : ((line y z 0).1 1)^2+((line y z 0).1 2)^2 ≠ 0 := by
    simpa [line, ← radius_sq y] using (sq_pos_of_pos hy).ne'
  refine (hQ.sqrt hne).congr_deriv ?_
  simp only [line, zero_smul, add_zero, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  change (2*y.1 1*z.1 1+2*y.1 2*z.1 2)/(2*radius y) = radialRate y z
  unfold radialRate
  ring

theorem hasDerivAt_time_line {m : ℕ} (y z : ThinCurrentSpace m) :
    HasDerivAt (fun t => time (line y z t)) (z.1 0) 0 :=
  (hasDerivAt_line_parameter y z 0).sub_const 1

theorem hasDerivAt_ratioRe_line {m : ℕ} {y : ThinCurrentSpace m}
    (hy : 0 < radius y) (z : ThinCurrentSpace m) (j : Fin m) :
    HasDerivAt (fun t => ratioRe (line y z t) j) (realRate y z j) 0 := by
  have hU := hasDerivAt_line_parameter y z 1
  have hV := hasDerivAt_line_parameter y z 2
  have hP := hasDerivAt_line_p y z (j,0)
  have hQ := hasDerivAt_line_p y z (j,1)
  have hne : ((line y z 0).1 1)^2+((line y z 0).1 2)^2 ≠ 0 := by
    simpa [line, ← radius_sq y] using (sq_pos_of_pos hy).ne'
  refine (((hU.mul hP).add (hV.mul hQ)).div ((hU.pow 2).add (hV.pow 2)) hne).congr_deriv ?_
  simp only [line, zero_smul, add_zero, Pi.mul_apply, Pi.add_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  unfold realRate radialRate angularRate ratioRe ratioIm
  rw [← radius_sq y]
  have hs := hy.ne'
  field_simp
  linear_combination (z.1 1*y.2.2 (j,0)+z.1 2*y.2.2 (j,1)) * radius_sq y

theorem hasDerivAt_ratioIm_line {m : ℕ} {y : ThinCurrentSpace m}
    (hy : 0 < radius y) (z : ThinCurrentSpace m) (j : Fin m) :
    HasDerivAt (fun t => ratioIm (line y z t) j) (imaginaryRate y z j) 0 := by
  have hU := hasDerivAt_line_parameter y z 1
  have hV := hasDerivAt_line_parameter y z 2
  have hP := hasDerivAt_line_p y z (j,0)
  have hQ := hasDerivAt_line_p y z (j,1)
  have hne : ((line y z 0).1 1)^2+((line y z 0).1 2)^2 ≠ 0 := by
    simpa [line, ← radius_sq y] using (sq_pos_of_pos hy).ne'
  refine (((hU.mul hQ).sub (hV.mul hP)).div ((hU.pow 2).add (hV.pow 2)) hne).congr_deriv ?_
  simp only [line, zero_smul, add_zero, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  unfold imaginaryRate radialRate angularRate ratioRe ratioIm
  rw [← radius_sq y]
  have hs := hy.ne'
  field_simp
  linear_combination (z.1 1*y.2.2 (j,1)-z.1 2*y.2.2 (j,0)) * radius_sq y

end KakeyaSharp.Packet
