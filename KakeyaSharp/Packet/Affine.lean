/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Coordinates

@[expose] public section

/-! The explicit affine map taking a packet phase to a Euclidean square. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp.Packet
open Matrix MeasureTheory

def scaleX (r h s τ : ℝ) : ℝ :=
  Real.sqrt h * Real.sqrt (denominator r s τ) / Real.sqrt (r+s)
def scaleRe (r h s : ℝ) : ℝ :=
  Real.sqrt h * Real.sqrt (r+s) / (Real.sqrt r * Real.sqrt s)
def scaleIm (h s : ℝ) : ℝ := Real.sqrt h / Real.sqrt s

theorem scaleX_sq {r h s : ℝ} (hr : 0 < r) (hh : 0 < h) (hs : 0 < s) (τ : ℝ) :
    scaleX r h s τ ^ 2 = h * denominator r s τ / (r+s) := by
  simp only [scaleX, div_pow, mul_pow, Real.sq_sqrt hh.le,
    Real.sq_sqrt (denominator_pos hr hs τ).le, Real.sq_sqrt (add_pos hr hs).le]

theorem scaleRe_sq {r h s : ℝ} (hr : 0 < r) (hh : 0 < h) (hs : 0 < s) :
    scaleRe r h s ^ 2 = h * (r+s) / (r*s) := by
  simp only [scaleRe, div_pow, mul_pow, Real.sq_sqrt hh.le,
    Real.sq_sqrt hr.le, Real.sq_sqrt hs.le, Real.sq_sqrt (add_pos hr hs).le]

theorem scaleIm_sq {h s : ℝ} (hh : 0 < h) (hs : 0 < s) :
    scaleIm h s ^ 2 = h/s := by
  simp only [scaleIm, div_pow, Real.sq_sqrt hh.le, Real.sq_sqrt hs.le]

def shapeBlock (r h s τ u w : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![scaleX r h s τ, τ*s/(r+s)*scaleRe r h s, 0;
     0, u*scaleRe r h s, -w*scaleIm h s;
     0, w*scaleRe r h s, u*scaleIm h s]

def packetJacobian (r h s τ : ℝ) : ℝ :=
  (Real.sqrt h)^3*s*Real.sqrt (denominator r s τ)/Real.sqrt r

theorem packetJacobian_pos {r h s : ℝ} (hr : 0 < r) (hh : 0 < h) (hs : 0 < s) (τ : ℝ) :
    0 < packetJacobian r h s τ := by
  have hd := denominator_pos hr hs τ
  unfold packetJacobian
  positivity

theorem det_shapeBlock {r h s τ u w : ℝ} (hr : 0 < r) (hh : 0 < h) (hs : 0 < s)
    (huw : u^2+w^2=s^2) : (shapeBlock r h s τ u w).det = packetJacobian r h s τ := by
  have hs0 := (Real.sqrt_pos.mpr hs).ne'
  have hr0 := (Real.sqrt_pos.mpr hr).ne'
  have hk0 := (Real.sqrt_pos.mpr (add_pos hr hs)).ne'
  have hs2 := Real.sq_sqrt hs.le
  calc
    _ = scaleX r h s τ * scaleRe r h s * scaleIm h s * (u^2+w^2) := by
      simp [shapeBlock, Matrix.det_fin_three]
      ring
    _ = _ := by
      rw [huw]
      unfold scaleX scaleRe scaleIm packetJacobian
      field_simp
      rw [hs2]

def shapeMatrix (m : ℕ) (r h s τ u w : ℝ) :
    Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ :=
  Matrix.blockDiagonal (fun _ : Fin m => shapeBlock r h s τ u w)

theorem det_shapeMatrix (m : ℕ) {r h s τ u w : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hs : 0 < s) (huw : u^2+w^2=s^2) :
    (shapeMatrix m r h s τ u w).det = packetJacobian r h s τ ^ m := by
  simp [shapeMatrix, Matrix.det_blockDiagonal, det_shapeBlock hr hh hs huw]

theorem shapeMatrix_mulVec (m : ℕ) (r h s τ u w : ℝ) (z : PacketCoordinates m)
    (b : Fin 3) (j : Fin m) :
    ((shapeMatrix m r h s τ u w).mulVec z) (b,j) =
      (shapeBlock r h s τ u w).mulVec (fun c => z (c,j)) b := by
  simp [shapeMatrix, Matrix.mulVec, dotProduct, Matrix.blockDiagonal,
    Fintype.sum_prod_type]

theorem scalarPhase_affine {r h s : ℝ} (hr : 0 < r) (hh : 0 < h) (hs : 0 < s)
    (τ a v x α β : ℝ) :
    scalarPhase r s τ a v
      (a+τ*v+scaleX r h s τ*x+τ*s/(r+s)*scaleRe r h s*α)
      (v+scaleRe r h s*α) (scaleIm h s*β) = h*(x^2+α^2+β^2) := by
  have hk := (add_pos hr hs).ne'
  have hd := (denominator_pos hr hs τ).ne'
  rw [scalarPhase_completed_square hr hs]
  have hx : a+τ*v+scaleX r h s τ*x+τ*s/(r+s)*scaleRe r h s*α-a-
      τ*(r*v+s*(v+scaleRe r h s*α))/(r+s) = scaleX r h s τ*x := by
    field_simp
    ring
  rw [hx]
  simp only [add_sub_cancel_left, mul_pow, scaleX_sq hr hh hs, scaleRe_sq hr hh hs,
    scaleIm_sq hh hs]
  field_simp
  ring

def packetTranslation {m : ℕ} (a v : Fin m → ℝ) (p : Space 3) : PacketCoordinates m :=
  fun k => ![a k.2+(p 0-1)*v k.2, p 1*v k.2, p 2*v k.2] k.1

def packetAffine {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (p : Space 3)
    (z : PacketCoordinates m) : ThinSpace m :=
  unpack m ((shapeMatrix m r h (radius (p,(0 : ThinSpace m))) (p 0-1) (p 1) (p 2)).mulVec z +
    packetTranslation a v p)

theorem packetAffine_x {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (p : Space 3)
    (z : PacketCoordinates m) (j : Fin m) :
    (packetAffine r h a v p z).1 j =
      a j+(p 0-1)*v j+scaleX r h (radius (p,(0 : ThinSpace m))) (p 0-1)*z (0,j)+
        (p 0-1)*radius (p,(0 : ThinSpace m))/(r+radius (p,(0 : ThinSpace m)))*
          scaleRe r h (radius (p,(0 : ThinSpace m)))*z (1,j) := by
  change (_ : ℝ)+_ = _
  rw [shapeMatrix_mulVec]
  simp [shapeBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three, packetTranslation]
  ring

theorem packetAffine_P0 {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (p : Space 3)
    (z : PacketCoordinates m) (j : Fin m) :
    (packetAffine r h a v p z).2 (j,0) =
      p 1*(v j+scaleRe r h (radius (p,(0 : ThinSpace m)))*z (1,j))-
        p 2*scaleIm h (radius (p,(0 : ThinSpace m)))*z (2,j) := by
  change (_ : ℝ)+_ = _
  rw [shapeMatrix_mulVec]
  simp [shapeBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three, packetTranslation]
  ring

theorem packetAffine_P1 {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (p : Space 3)
    (z : PacketCoordinates m) (j : Fin m) :
    (packetAffine r h a v p z).2 (j,1) =
      p 2*(v j+scaleRe r h (radius (p,(0 : ThinSpace m)))*z (1,j))+
        p 1*scaleIm h (radius (p,(0 : ThinSpace m)))*z (2,j) := by
  change (_ : ℝ)+_ = _
  rw [shapeMatrix_mulVec]
  simp [shapeBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three, packetTranslation]
  ring

theorem ratioRe_packetAffine {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) {p : Space 3}
    (hp : 0 < radius (p,(0 : ThinSpace m))) (z : PacketCoordinates m) (j : Fin m) :
    ratioRe (p,packetAffine r h a v p z) j =
      v j+scaleRe r h (radius (p,(0 : ThinSpace m)))*z (1,j) := by
  have hq : (p 1)^2+(p 2)^2 ≠ 0 := (Real.sqrt_pos.mp hp).ne'
  unfold ratioRe
  rw [packetAffine_P0, packetAffine_P1]
  field_simp
  ring

theorem ratioIm_packetAffine {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) {p : Space 3}
    (hp : 0 < radius (p,(0 : ThinSpace m))) (z : PacketCoordinates m) (j : Fin m) :
    ratioIm (p,packetAffine r h a v p z) j =
      scaleIm h (radius (p,(0 : ThinSpace m)))*z (2,j) := by
  have hq : (p 1)^2+(p 2)^2 ≠ 0 := (Real.sqrt_pos.mp hp).ne'
  unfold ratioIm
  rw [packetAffine_P0, packetAffine_P1]
  field_simp
  ring

def packetSquare {m : ℕ} (z : PacketCoordinates m) : ℝ := ∑ k, z k ^ 2

theorem physicalPhase_packetAffine {m : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (a v : Fin m → ℝ) {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m)))
    (z : PacketCoordinates m) :
    physicalPhase r a v (p,packetAffine r h a v p z) = h*packetSquare z := by
  unfold physicalPhase phase
  simp only [packetAffine_x, ratioRe_packetAffine r h a v hp, ratioIm_packetAffine r h a v hp]
  change (∑ j, scalarPhase r (radius (p,(0 : ThinSpace m))) (p 0-1) _ _ _ _ _) = _
  simp only [scalarPhase_affine hr hh hp, packetSquare, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

theorem prefactor_jacobian (m : ℕ) {r h s : ℝ} (hr : 0 < r) (_hh : 0 < h) (hs : 0 < s)
    (τ : ℝ) : prefactor m r s τ * packetJacobian r h s τ ^ m =
      ((Real.sqrt h)^3/Real.sqrt r)^m := by
  have hd := denominator_pos hr hs τ
  have hb : 0 < s*Real.sqrt (denominator r s τ) := mul_pos hs (Real.sqrt_pos.mpr hd)
  have he : s^2*denominator r s τ = (s*Real.sqrt (denominator r s τ))^2 := by
    rw [mul_pow, Real.sq_sqrt hd.le]
  have hp : prefactor m r s τ = ((s*Real.sqrt (denominator r s τ))^m)⁻¹ := by
    rw [prefactor, he, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ)*(-(m : ℝ)/2) = -(m : ℝ) by ring,
      Real.rpow_neg hb.le, Real.rpow_natCast]
  rw [hp]
  have hj : packetJacobian r h s τ =
      (s*Real.sqrt (denominator r s τ))*((Real.sqrt h)^3/Real.sqrt r) := by
    unfold packetJacobian
    ring
  have hjm := congrArg (fun x : ℝ => x^m) hj
  rw [mul_pow] at hjm
  rw [hjm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hb.ne'), one_mul]

end KakeyaSharp.Packet
