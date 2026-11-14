/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Trace.LogBarrier
public import KakeyaSharp.Packet.Physical

@[expose] public section

/-! The actual input logarithmic barrier, in every unit transverse
orientation. Its Hessian, positivity and determinant are derived from
Fréchet derivatives, with no rotation-covariance assumption. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
namespace KakeyaSharp.Packet
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff

def inputRealLinear (m : ℕ) (a b : ℝ) : ThinSpace m →ₗ[ℝ] Space m where
  toFun z := WithLp.toLp 2 (fun i => z.1 i+a*z.2 (i,0)+b*z.2 (i,1))
  map_add' z w := by ext i; simp; ring
  map_smul' c z := by ext i; simp; ring

def inputImagLinear (m : ℕ) (a b : ℝ) : ThinSpace m →ₗ[ℝ] Space m where
  toFun z := WithLp.toLp 2 (fun i => a*z.2 (i,1)-b*z.2 (i,0))
  map_add' z w := by ext i; simp; ring
  map_smul' c z := by ext i; simp; ring

def inputReal (m : ℕ) (a b : ℝ) : ThinSpace m →L[ℝ] Space m :=
  (inputRealLinear m a b).toContinuousLinearMap

def inputImag (m : ℕ) (a b : ℝ) : ThinSpace m →L[ℝ] Space m :=
  (inputImagLinear m a b).toContinuousLinearMap

theorem inputReal_direction {m : ℕ} (a b : ℝ) (i : Fin m) (α : Fin 3) :
    inputReal m a b (thinDirection i α) = ![1,a,b] α • EuclideanSpace.single i 1 := by
  fin_cases α <;> ext j <;>
    simp [inputReal, inputRealLinear, thinDirection]

theorem inputImag_direction {m : ℕ} (a b : ℝ) (i : Fin m) (α : Fin 3) :
    inputImag m a b (thinDirection i α) = ![0,-b,a] α • EuclideanSpace.single i 1 := by
  fin_cases α <;> ext j <;>
    simp [inputImag, inputImagLinear, thinDirection]

def inputQuadratic {m : ℕ} (a b : ℝ) : ThinSpace m → ℝ :=
  projectedQuadratic (inputReal m a b) 0 1 + projectedQuadratic (inputImag m a b) 0 2

theorem inputQuadratic_apply {m : ℕ} (a b : ℝ) (z : ThinSpace m) :
    inputQuadratic a b z = ∑ i : Fin m, ((z.1 i+a*z.2 (i,0)+b*z.2 (i,1))^2 +
      2*(a*z.2 (i,1)-b*z.2 (i,0))^2) := by
  simp [inputQuadratic, projectedQuadratic, EuclideanSpace.real_norm_sq_eq,
    Finset.sum_add_distrib, Finset.mul_sum, inputReal, inputImag, inputRealLinear, inputImagLinear]

theorem inputQuadratic_nonneg {m : ℕ} (a b : ℝ) (z : ThinSpace m) : 0 ≤ inputQuadratic a b z := by
  dsimp [inputQuadratic, projectedQuadratic]
  positivity

theorem inputQuadratic_smooth (m : ℕ) (a b : ℝ) : ContDiff ℝ ∞ (inputQuadratic (m := m) a b) :=
  (projectedQuadratic_smooth _ _ _).add (projectedQuadratic_smooth _ _ _)

theorem inputQuadratic_hessian {m : ℕ} {a b : ℝ} (hab : a^2+b^2=1) (z : ThinSpace m) :
    thinQuaternionHessian (inputQuadratic a b) z =
      (8 : ℝ) • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) := by
  rw [inputQuadratic, thinQuaternionHessian_add
    ((projectedQuadratic_smooth _ _ _).of_le (by norm_num))
    ((projectedQuadratic_smooth _ _ _).of_le (by norm_num))]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, thinQuaternionHessian, hessianMap, thinRealHessian,
    hessian_projectedQuadratic, Fin.sum_univ_three]
  by_cases hij : i=j
  · subst j
    ext <;> simp [threeSlots, inputReal_direction, inputImag_direction,
      EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left,
      real_inner_smul_right, norm_smul, Real.norm_eq_abs, sq_abs] <;> nlinarith [hab]
  · ext <;> simp [threeSlots, inputReal_direction, inputImag_direction,
      EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left,
      real_inner_smul_right, hij, Ne.symm hij]

theorem inputQuadratic_gradient {m : ℕ} (a b : ℝ) (z : ThinSpace m) (i : Fin m) :
    thinQuaternionGradient (inputQuadratic a b) z i =
      ⟨2*(z.1 i+a*z.2 (i,0)+b*z.2 (i,1)),
        2*a*(z.1 i+a*z.2 (i,0)+b*z.2 (i,1))-4*b*(a*z.2 (i,1)-b*z.2 (i,0)),
        2*b*(z.1 i+a*z.2 (i,0)+b*z.2 (i,1))+4*a*(a*z.2 (i,1)-b*z.2 (i,0)), 0⟩ := by
  have hd : fderiv ℝ (inputQuadratic a b) z =
      fderiv ℝ (projectedQuadratic (inputReal m a b) 0 1) z +
      fderiv ℝ (projectedQuadratic (inputImag m a b) 0 2) z :=
    fderiv_add ((projectedQuadratic_smooth _ _ _).differentiable (by simp) z)
      ((projectedQuadratic_smooth _ _ _).differentiable (by simp) z)
  unfold thinQuaternionGradient
  rw [hd, gradientMap_threeSlots]
  ext <;> simp [fderiv_projectedQuadratic, inputReal_direction, inputImag_direction,
    EuclideanSpace.inner_single_right, real_inner_smul_right]
  all_goals simp [inputReal, inputImag, inputRealLinear, inputImagLinear]
  all_goals ring

theorem inputQuadratic_gradient_size {m : ℕ} {a b : ℝ} (hab : a^2+b^2=1) (z : ThinSpace m) :
    quaternionSize (thinQuaternionGradient (inputQuadratic a b) z) = 8*inputQuadratic a b z := by
  rw [quaternionSize, inputQuadratic_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inputQuadratic_gradient, pow_two, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  dsimp only
  calc
    _ = (4+4*(a^2+b^2))*(z.1 i+a*z.2 (i,0)+b*z.2 (i,1))^2 +
        16*(a^2+b^2)*(a*z.2 (i,1)-b*z.2 (i,0))^2 := by ring
    _ = _ := by rw [hab]; ring

theorem inputQuadratic_le {m : ℕ} {a b : ℝ} (hab : a^2+b^2=1) (z : ThinSpace m) :
    inputQuadratic a b z ≤ 2*(‖z.1‖^2+‖z.2‖^2) := by
  rw [inputQuadratic_apply, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he : (a*z.2 (i,0)+b*z.2 (i,1))^2+(a*z.2 (i,1)-b*z.2 (i,0))^2 =
      (z.2 (i,0))^2+(z.2 (i,1))^2 := by
    calc
      _ = (a^2+b^2)*((z.2 (i,0))^2+(z.2 (i,1))^2) := by ring
      _ = _ := by rw [hab,one_mul]
  nlinarith [sq_nonneg (z.1 i-(a*z.2 (i,0)+b*z.2 (i,1)))]

def inputBarrier {m : ℕ} (h R a b : ℝ) : ThinSpace m → ℝ :=
  thinLogBarrier h (2*R^2) (inputQuadratic a b)

theorem inputBarrier_smooth {m : ℕ} {h : ℝ} (hh : 0 < h) (R a b : ℝ) :
    ContDiff ℝ ∞ (inputBarrier (m := m) h R a b) :=
  thinLogBarrier_smooth hh (inputQuadratic_smooth m a b) (inputQuadratic_nonneg a b)

theorem inputBarrier_bounds {m : ℕ} {h R a b : ℝ} (hh : 0 < h) (hab : a^2+b^2=1)
    {z : ThinSpace m} (hz : z ∈ thinClosedBallAt R 0) :
    -Real.log ((h+2*R^2)/h) ≤ inputBarrier h R a b z ∧ inputBarrier h R a b z ≤ 0 := by
  apply thinLogBarrier_bounds hh (inputQuadratic_nonneg a b z)
  have hz' : ‖z.1‖^2+‖z.2‖^2 ≤ R^2 := by
    simpa only [thinClosedBallAt, mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero, sub_zero] using hz
  exact (inputQuadratic_le hab z).trans (by linarith)

theorem inputBarrier_positive {m : ℕ} {h R a b : ℝ} (hh : 0 < h) (hab : a^2+b^2=1)
    (z : ThinSpace m) (w : Fin m → Quaternion ℝ) :
    0 ≤ quaternionForm (thinQuaternionHessian (inputBarrier h R a b) z) w := by
  have h := thinLogBarrier_hessian_lower (Q := 2*R^2) hh
    ((inputQuadratic_smooth m a b).of_le (by simp)) (inputQuadratic_nonneg a b z)
    (inputQuadratic_hessian hab z) (inputQuadratic_gradient_size hab z) w
  exact le_trans (mul_nonneg (by positivity) (quaternionSize_nonneg w)) h

theorem inputBarrier_determinant {m : ℕ} (hm : 1 ≤ m) {h R a b : ℝ}
    (hh : 0 < h) (hab : a^2+b^2=1) (z : ThinSpace m) :
    mooreDet m (thinQuaternionHessian (inputBarrier h R a b) z) =
      (8 : ℝ)^m*h/(h+inputQuadratic a b z)^(m+1) :=
  thinLogBarrier_determinant hm hh (by norm_num)
    ((inputQuadratic_smooth m a b).of_le (by simp)) (inputQuadratic_nonneg a b z)
    (inputQuadratic_hessian hab z) (inputQuadratic_gradient_size hab z)

theorem inputQuadratic_eq_ratios {m : ℕ} {p : Space 3}
    (hp : (p 1)^2+(p 2)^2=1) (z : ThinSpace m) :
    inputQuadratic (p 1) (p 2) z =
      ∑ i : Fin m, ((z.1 i+ratioRe (p,z) i)^2+2*(ratioIm (p,z) i)^2) := by
  rw [inputQuadratic_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ratioRe, ratioIm, hp, div_one]
  ring

theorem inputBarrier_value_bound {m : ℕ} (hm : 1 ≤ m) {h R a b : ℝ}
    (hh : 0 < h) (hR : 0 < R) (hab : a^2+b^2=1) {μ w : ThinSpace m → ℝ}
    (hμ : ContinuousOn μ (thinClosedBallAt R 0))
    (hw : ∀ z ∈ thinBallAt R 0, 0 ≤ w z)
    (hdom : ∀ z ∈ thinBallAt R 0, μ z ≤ w z*((8 : ℝ)^m*h/(h+inputQuadratic a b z)^(m+1)))
    (hi : IntegrableOn (fun z => (w z)^(((m : ℝ)+1)/m)*
      ((8 : ℝ)^m*h/(h+inputQuadratic a b z)^(m+1))) (thinBallAt R 0)) :
    thinValueRealAt R 0 μ ≤ thinWeightedConstant m*Real.log ((h+2*R^2)/h)*
      ∫ z in thinBallAt R 0, (w z)^(((m : ℝ)+1)/m)*
        ((8 : ℝ)^m*h/(h+inputQuadratic a b z)^(m+1)) := by
  have hH : 0 ≤ Real.log ((h+2*R^2)/h) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hh).mpr
    nlinarith [sq_nonneg R]
  have hD := inputBarrier_determinant (R := R) hm hh hab
  have hd : ∀ z ∈ thinBallAt R 0, μ z ≤ w z*mooreDet m
      (thinQuaternionHessian (inputBarrier h R a b) z) := by
    simpa only [hD] using hdom
  have hi' : IntegrableOn (fun z => (w z)^(((m : ℝ)+1)/m)*mooreDet m
      (thinQuaternionHessian (inputBarrier h R a b) z)) (thinBallAt R 0) := by
    simpa only [hD] using hi
  have hv := thinValueRealAt_weighted_bound hm hR hH (0 : ThinSpace m)
    (fun z _ => (inputBarrier_smooth hh R a b).contDiffAt.of_le (by simp))
    (fun _ hz => inputBarrier_bounds hh hab hz) (fun z _ v => inputBarrier_positive hh hab z v)
    hμ hw hd hi'
  simpa only [hD] using hv

def inputLogConstant (R : ℝ) : ℝ := 4+Real.log (1+2*R^2)/Real.log 2

theorem inputLogConstant_pos (R : ℝ) : 0 < inputLogConstant R := by
  have hlog : 0 ≤ Real.log (1+2*R^2) := Real.log_nonneg (by nlinarith [sq_nonneg R])
  have ht : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold inputLogConstant
  positivity

theorem inputBarrier_height_le_log {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log ((δ^4+2*R^2)/δ^4) ≤ inputLogConstant R*Real.log (2/δ) := by
  have hd4 : 0 < δ^4 := pow_pos hδ _
  have hd41 : δ^4 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hpos : 0 < δ^4+2*R^2 := by positivity
  have hbig : 0 < 1+2*R^2 := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hpos hbig (by linarith : δ^4+2*R^2 ≤ 1+2*R^2)
  have hdlog : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hlog0 : 0 ≤ Real.log (1+2*R^2) := Real.log_nonneg (by nlinarith [sq_nonneg R])
  have ht : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hprod := mul_nonneg (div_nonneg hlog0 ht.le) (neg_nonneg.mpr hdlog)
  have he : (Real.log (1+2*R^2)/Real.log 2)*Real.log 2=Real.log (1+2*R^2) :=
    div_mul_cancel₀ _ ht.ne'
  rw [Real.log_div hpos.ne' hd4.ne', Real.log_pow,
    Real.log_div (by norm_num) hδ.ne', inputLogConstant]
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem inputBarrier_value_le_log {m : ℕ} (hm : 1 ≤ m) {δ R a b : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 < R) (hab : a^2+b^2=1) {μ w : ThinSpace m → ℝ}
    (hμ : ContinuousOn μ (thinClosedBallAt R 0))
    (hw : ∀ z ∈ thinBallAt R 0, 0 ≤ w z)
    (hdom : ∀ z ∈ thinBallAt R 0, μ z ≤ w z*((8 : ℝ)^m*δ^4/(δ^4+inputQuadratic a b z)^(m+1)))
    (hi : IntegrableOn (fun z => (w z)^(((m : ℝ)+1)/m)*
      ((8 : ℝ)^m*δ^4/(δ^4+inputQuadratic a b z)^(m+1))) (thinBallAt R 0)) :
    thinValueRealAt R 0 μ ≤ (thinWeightedConstant m*inputLogConstant R)*Real.log (2/δ)*
      ∫ z in thinBallAt R 0, (w z)^(((m : ℝ)+1)/m)*
        ((8 : ℝ)^m*δ^4/(δ^4+inputQuadratic a b z)^(m+1)) := by
  have hv := inputBarrier_value_bound hm (pow_pos hδ 4) hR hab hμ hw hdom hi
  have hi0 : 0 ≤ ∫ z in thinBallAt R 0, (w z)^(((m : ℝ)+1)/m)*
      ((8 : ℝ)^m*δ^4/(δ^4+inputQuadratic a b z)^(m+1)) := by
    apply setIntegral_nonneg (thinBallAt_measurable R 0)
    intro z hz
    have hq := inputQuadratic_nonneg a b z
    exact mul_nonneg (Real.rpow_nonneg (hw z hz) _) (by positivity)
  apply hv.trans
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (inputBarrier_height_le_log (R := R) hδ hδ1) (thinWeightedConstant_pos hm).le) hi0
  simpa only [mul_assoc] using h

end KakeyaSharp.Packet
