/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.InputDomination

@[expose] public section

/-! Volume-preserving coordinates separating the directional variable
from the two normal variables at the input. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
namespace KakeyaSharp.Packet
open Matrix MeasureTheory

def inputCoordinateLinearEquiv (m : ℕ) (a b : ℝ) (hab : a^2+b^2=1) :
    ThinSpace m ≃ₗ[ℝ] ThinSpace m where
  toFun y := (WithLp.toLp 2 (fun i => y.2 (i,0)-y.1 i),
    WithLp.toLp 2 (fun q => ![a*y.1 q.1-b*y.2 (q.1,1), b*y.1 q.1+a*y.2 (q.1,1)] q.2))
  invFun z := (WithLp.toLp 2 (fun i => a*z.2 (i,0)+b*z.2 (i,1)),
    WithLp.toLp 2 (fun q => ![z.1 q.1+a*z.2 (q.1,0)+b*z.2 (q.1,1),
      a*z.2 (q.1,1)-b*z.2 (q.1,0)] q.2))
  left_inv y := by
    apply Prod.ext
    · ext i
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linear_combination y.1 i*hab
    · ext ⟨i,k⟩
      fin_cases k <;> simp
      · linear_combination y.1 i*hab
      · linear_combination y.2 (i,1)*hab
  right_inv z := by
    apply Prod.ext
    · ext i
      simp
    · ext ⟨i,k⟩
      fin_cases k <;> simp
      · linear_combination z.2 (i,0)*hab
      · linear_combination z.2 (i,1)*hab
  map_add' y z := by
    apply Prod.ext
    · ext i
      simp
      ring
    · ext ⟨i,k⟩
      fin_cases k <;> simp <;> ring
  map_smul' c y := by
    apply Prod.ext
    · ext i
      simp
      ring
    · ext ⟨i,k⟩
      fin_cases k <;> simp <;> ring

def inputCoordinates (m : ℕ) (a b : ℝ) (hab : a^2+b^2=1) :
    ThinSpace m ≃L[ℝ] ThinSpace m :=
  (inputCoordinateLinearEquiv m a b hab).toContinuousLinearEquiv

def inputCoordinateBlock (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1,1,0; a,0,-b; b,0,a]

def inputCoordinateMatrix (m : ℕ) (a b : ℝ) : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ :=
  Matrix.blockDiagonal (fun _ : Fin m => inputCoordinateBlock a b)

theorem inputCoordinateMatrix_det (m : ℕ) {a b : ℝ} (hab : a^2+b^2=1) :
    (inputCoordinateMatrix m a b).det = (-1 : ℝ)^m := by
  have he : (inputCoordinateBlock a b).det = -1 := by
    rw [Matrix.det_fin_three]
    change (-1)*0*a-(-1)*(-b)*0-1*a*a+1*(-b)*b+0*a*0-0*0*b = -1
    nlinarith
  simp [inputCoordinateMatrix, Matrix.det_blockDiagonal, he]

theorem inputCoordinates_unpack (m : ℕ) {a b : ℝ} (hab : a^2+b^2=1) (z : PacketCoordinates m) :
    inputCoordinates m a b hab (unpack m z) =
      unpack m ((inputCoordinateMatrix m a b).mulVec z) := by
  have he (k : Fin 3) (i : Fin m) : ((inputCoordinateMatrix m a b).mulVec z) (k,i) =
      (inputCoordinateBlock a b).mulVec (fun c => z (c,i)) k := by
    simp [inputCoordinateMatrix, Matrix.mulVec, dotProduct, Matrix.blockDiagonal, Fintype.sum_prod_type]
  apply Prod.ext
  · ext i
    change z (1,i)-z (0,i) = ((inputCoordinateMatrix m a b).mulVec z) (0,i)
    rw [he]
    simp [inputCoordinateBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  · ext ⟨i,k⟩
    fin_cases k
    · change a*z (0,i)-b*z (2,i) = ((inputCoordinateMatrix m a b).mulVec z) (1,i)
      rw [he]
      simp [inputCoordinateBlock,Matrix.mulVec,dotProduct,Fin.sum_univ_three,sub_eq_add_neg]
    · change b*z (0,i)+a*z (2,i) = ((inputCoordinateMatrix m a b).mulVec z) (2,i)
      rw [he]
      simp [inputCoordinateBlock,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem inputCoordinates_measurePreserving (m : ℕ) {a b : ℝ} (hab : a^2+b^2=1) :
    MeasurePreserving (inputCoordinates m a b hab) volume volume := by
  have hdet : (inputCoordinateMatrix m a b).det ≠ 0 := by
    rw [inputCoordinateMatrix_det m hab]
    exact pow_ne_zero _ (by norm_num)
  have hlin : MeasurePreserving (Matrix.toLin' (inputCoordinateMatrix m a b)) volume volume := by
    refine ⟨(Matrix.toLin' (inputCoordinateMatrix m a b)).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, inputCoordinateMatrix_det m hab]
    simp
  have hi := MeasurePreserving.symm (unpack m).toHomeomorph.toMeasurableEquiv
    (unpack_measurePreserving m)
  have he := (unpack_measurePreserving m).comp (hlin.comp hi)
  convert he using 1
  funext z
  simpa using inputCoordinates_unpack m hab ((unpack m).symm z)

theorem inputAlpha_inputCoordinates {m : ℕ} {p : Space 3}
    (hp : (p 1)^2+(p 2)^2=1) (y : ThinSpace m) :
    inputAlpha p (inputCoordinates m (p 1) (p 2) hp y) = y.1 := by
  ext i
  change ((p 1)*(p 1*y.1 i-p 2*y.2 (i,1))+
    (p 2)*(p 2*y.1 i+p 1*y.2 (i,1)))/((p 1)^2+(p 2)^2)=y.1 i
  rw [hp,div_one]
  linear_combination y.1 i*hp

theorem inputQuadratic_inputCoordinates {m : ℕ} {a b : ℝ}
    (hab : a^2+b^2=1) (y : ThinSpace m) :
    inputQuadratic a b (inputCoordinates m a b hab y) =
      ∑ i, ((y.2 (i,0))^2+2*(y.2 (i,1))^2) := by
  rw [inputQuadratic_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hα : a*(a*y.1 i-b*y.2 (i,1))+b*(b*y.1 i+a*y.2 (i,1))=y.1 i := by
    linear_combination y.1 i*hab
  have hβ : a*(b*y.1 i+a*y.2 (i,1))-b*(a*y.1 i-b*y.2 (i,1))=y.2 (i,1) := by
    linear_combination y.2 (i,1)*hab
  change ((y.2 (i,0)-y.1 i)+a*(a*y.1 i-b*y.2 (i,1))+b*(b*y.1 i+a*y.2 (i,1)))^2+
      2*(a*(b*y.1 i+a*y.2 (i,1))-b*(a*y.1 i-b*y.2 (i,1)))^2 = _
  rw [hβ]
  have he : (y.2 (i,0)-y.1 i)+a*(a*y.1 i-b*y.2 (i,1))+b*(b*y.1 i+a*y.2 (i,1))=y.2 (i,0) := by linarith
  rw [he]

theorem norm_sq_le_inputQuadratic_inputCoordinates {m : ℕ} {a b : ℝ}
    (hab : a^2+b^2=1) (y : ThinSpace m) :
    ‖y.2‖^2 ≤ inputQuadratic a b (inputCoordinates m a b hab y) := by
  rw [inputQuadratic_inputCoordinates hab, EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (y.2 (i,1))]

end KakeyaSharp.Packet
