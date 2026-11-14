/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.CoordinateDerivative

@[expose] public section

/-! Actual derivatives of each entry of the packet column. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp.Packet
open KakeyaSharp.QuaternionAlgebra

def centerRate {m : ℕ} (r : ℝ) (a v : Fin m → ℝ)
    (y z : ThinCurrentSpace m) (j : Fin m) : ℝ :=
  ((r+radius y)*(radialRate y z*(ratioRe y j-centers r a v y j)+
      radius y*realRate y z j+z.1 0*residuals r a v y j)+
    time y*(z.2.1 j-z.1 0*centers r a v y j-radialRate y z*residuals r a v y j))/
      denominator r (radius y) (time y)

def residualRate {m : ℕ} (r : ℝ) (a v : Fin m → ℝ)
    (y z : ThinCurrentSpace m) (j : Fin m) : ℝ :=
  ((r+radius y)*(z.2.1 j-z.1 0*centers r a v y j-radialRate y z*residuals r a v y j)-
    time y*(radialRate y z*(ratioRe y j-centers r a v y j)+
      radius y*realRate y z j+z.1 0*residuals r a v y j))/
      denominator r (radius y) (time y)

def columnVariation (u v d u' v' α' β' c' d' : ℝ) : Q :=
  ⟨(α'+c')/2,-(u'*d+u*d')/2,-(v'*d+v*d')/2,β'/2⟩

def columnRate {m : ℕ} (r : ℝ) (a v : Fin m → ℝ)
    (y z : ThinCurrentSpace m) (j : Fin m) : Q :=
  columnVariation (y.1 1/radius y) (y.1 2/radius y) (residuals r a v y j)
    ((z.1 1*radius y-y.1 1*radialRate y z)/(radius y)^2)
    ((z.1 2*radius y-y.1 2*radialRate y z)/(radius y)^2)
    (realRate y z j) (imaginaryRate y z j) (centerRate r a v y z j) (residualRate r a v y z j)

theorem hasDerivAt_centers_line {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (z : ThinCurrentSpace m) (j : Fin m) :
    HasDerivAt (fun t => centers r a v (line y z t) j) (centerRate r a v y z j) 0 := by
  have he : line y z 0=y := by simp [line]
  exact hasDerivAt_center_curve (a := a j) (v := v j) hr
    (hasDerivAt_radius_line hy z) (hasDerivAt_time_line y z)
    (hasDerivAt_line_x y z j) (hasDerivAt_ratioRe_line hy z j)
    (congrArg radius he) (congrArg time he) (congrArg (fun w => w.2.1 j) he)
    (congrArg (fun w => ratioRe w j) he) hy

theorem hasDerivAt_residuals_line {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (z : ThinCurrentSpace m) (j : Fin m) :
    HasDerivAt (fun t => residuals r a v (line y z t) j) (residualRate r a v y z j) 0 := by
  have he : line y z 0=y := by simp [line]
  exact hasDerivAt_residual_curve (a := a j) (v := v j) hr
    (hasDerivAt_radius_line hy z) (hasDerivAt_time_line y z)
    (hasDerivAt_line_x y z j) (hasDerivAt_ratioRe_line hy z j)
    (congrArg radius he) (congrArg time he) (congrArg (fun w => w.2.1 j) he)
    (congrArg (fun w => ratioRe w j) he) hy

theorem hasDerivAt_columnEntry_curve {U V A B C D : ℝ → ℝ}
    {u' v' α' β' c' d' t : ℝ}
    (hU : HasDerivAt U u' t) (hV : HasDerivAt V v' t)
    (hA : HasDerivAt A α' t) (hB : HasDerivAt B β' t)
    (hC : HasDerivAt C c' t) (hD : HasDerivAt D d' t) :
    HasDerivAt (fun x => columnEntry (U x) (V x) (A x) (B x) (C x) (D x))
      (columnVariation (U t) (V t) (D t) u' v' α' β' c' d') t := by
  simp only [columnEntry_linear]
  have h := (((((hA.add hC).div_const 2).smul_const (1 : Q)).add
    (((hU.mul hD).neg.div_const 2).smul_const (threeSlots 1))).add
    (((hV.mul hD).neg.div_const 2).smul_const (threeSlots 2))).add
    ((hB.div_const 2).smul_const unitK)
  simp only [Pi.add_apply, Pi.neg_apply, Pi.mul_apply, neg_mul] at h ⊢
  refine h.congr_deriv ?_
  ext <;> simp [columnVariation, threeSlots, unitK]

theorem hasDerivAt_physicalColumn_line {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (z : ThinCurrentSpace m) (j : Fin m) :
    HasDerivAt (fun t => physicalColumn r a v (line y z t) j.succ) (columnRate r a v y z j) 0 := by
  have he : line y z 0=y := by simp [line]
  have hS := hasDerivAt_radius_line hy z
  have hne : radius (line y z 0) ≠ 0 := by simpa only [he] using hy.ne'
  have hU := (hasDerivAt_line_parameter y z 1).div hS hne
  have hV := (hasDerivAt_line_parameter y z 2).div hS hne
  have h := hasDerivAt_columnEntry_curve hU hV (hasDerivAt_ratioRe_line hy z j)
    (hasDerivAt_ratioIm_line hy z j) (hasDerivAt_centers_line hr a v hy z j)
    (hasDerivAt_residuals_line hr a v hy z j)
  simpa only [Pi.div_apply, he, columnRate, physicalColumn, column, Fin.cases_succ] using h

theorem physicalColumn_fderiv {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (z : ThinCurrentSpace m) (j : Fin m) :
    fderiv ℝ (fun w => physicalColumn r a v w j.succ) y z = columnRate r a v y z j :=
  fderiv_eq_of_line ((physicalColumn_contDiffAt (n := 1) hr a v hy j.succ).differentiableAt (by norm_num))
    (hasDerivAt_physicalColumn_line hr a v hy z j)

end KakeyaSharp.Packet
