/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Trace.Weighted

@[expose] public section

/-! Logarithmic barriers with an exact determinant. The differential
identities are stated for the actual three-slot Hessian and gradient. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff

theorem thinQuaternionHessian_log {m : ℕ} {f : ThinSpace m → ℝ}
    (hf : ContDiff ℝ 2 f) {z : ThinSpace m} (hz : f z ≠ 0) :
    thinQuaternionHessian (fun x => Real.log (f x)) z =
      (f z)⁻¹ • thinQuaternionHessian f z -
        (f z^2)⁻¹ • outer (thinQuaternionGradient f z) := by
  have he : thinRealHessian (fun x => Real.log (f x)) z =
      (f z)⁻¹ • thinRealHessian f z +
      (-(f z^2)⁻¹) • Matrix.of (fun p q => fderiv ℝ f z (thinDirection p.1 p.2)*
        fderiv ℝ f z (thinDirection q.1 q.2)) := by
    ext p q
    change fderiv ℝ (fderiv ℝ (fun x => Real.log (f x))) z _ _ = _
    rw [hessian_log hf hz]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, thinRealHessian]
    ring
  change hessianMap threeSlots _ = _
  rw [he, hessianMap_add, hessianMap_smul, hessianMap_smul]
  change (f z)⁻¹ • thinQuaternionHessian f z + (-(f z^2)⁻¹) •
    hessianMap threeSlots (fun p q => fderiv ℝ f z (thinDirection p.1 p.2)*
      fderiv ℝ f z (thinDirection q.1 q.2)) = _
  rw [hessianMap_rankOne threeSlots (fun p => fderiv ℝ f z (thinDirection p.1 p.2))]
  simp only [neg_smul, sub_eq_add_neg]
  rfl

def thinLogBarrier {m : ℕ} (h Q : ℝ) (ρ : ThinSpace m → ℝ) : ThinSpace m → ℝ :=
  fun z => Real.log (h+ρ z)-Real.log (h+Q)

theorem thinLogBarrier_smooth {m : ℕ} {h Q : ℝ} (hh : 0 < h) {ρ : ThinSpace m → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hρ0 : ∀ z, 0 ≤ ρ z) : ContDiff ℝ ∞ (thinLogBarrier h Q ρ) :=
  ((contDiff_const.add hρ).log (fun z => (add_pos_of_pos_of_nonneg hh (hρ0 z)).ne')).sub contDiff_const

theorem thinLogBarrier_bounds {m : ℕ} {h Q : ℝ} (hh : 0 < h) {ρ : ThinSpace m → ℝ}
    {z : ThinSpace m} (hρ0 : 0 ≤ ρ z) (hρQ : ρ z ≤ Q) :
    -Real.log ((h+Q)/h) ≤ thinLogBarrier h Q ρ z ∧ thinLogBarrier h Q ρ z ≤ 0 := by
  have hQ : 0 < h+Q := by linarith
  have hz : 0 < h+ρ z := by positivity
  have hlo := Real.strictMonoOn_log.monotoneOn hh hz (le_add_of_nonneg_right hρ0)
  have hhi := Real.strictMonoOn_log.monotoneOn hz hQ (show h+ρ z ≤ h+Q by linarith)
  rw [Real.log_div hQ.ne' hh.ne']
  dsimp [thinLogBarrier]
  constructor <;> linarith

theorem thinLogBarrier_hessian {m : ℕ} {h Q κ : ℝ} (hh : 0 < h)
    {ρ : ThinSpace m → ℝ} (hρ : ContDiff ℝ 2 ρ) {z : ThinSpace m} (hρ0 : 0 ≤ ρ z)
    (hD : thinQuaternionHessian ρ z = κ • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ))) :
    thinQuaternionHessian (thinLogBarrier h Q ρ) z =
      (κ/(h+ρ z)) • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) -
        (1/(h+ρ z)^2) • outer (thinQuaternionGradient ρ z) := by
  have hpos : 0 < h+ρ z := by positivity
  have hd : fderiv ℝ (fun x => h+ρ x) = fderiv ℝ ρ := by
    funext x
    exact fderiv_const_add h
  have hH : thinQuaternionHessian (fun x => h+ρ x) z = thinQuaternionHessian ρ z := by
    unfold thinQuaternionHessian thinRealHessian
    rw [hd]
  have hG : thinQuaternionGradient (fun x => h+ρ x) z = thinQuaternionGradient ρ z := by
    unfold thinQuaternionGradient
    rw [hd]
  change thinQuaternionHessian (fun x => Real.log (h+ρ x)-Real.log (h+Q)) z = _
  rw [thinQuaternionHessian_sub_const,
    thinQuaternionHessian_log (contDiff_const.add hρ) hpos.ne', hH, hG, hD, smul_smul]
  simp only [div_eq_mul_inv, one_mul, mul_comm κ]

theorem thinLogBarrier_hessian_lower {m : ℕ} {h Q κ : ℝ} (hh : 0 < h)
    {ρ : ThinSpace m → ℝ} (hρ : ContDiff ℝ 2 ρ) {z : ThinSpace m} (hρ0 : 0 ≤ ρ z)
    (hD : thinQuaternionHessian ρ z = κ • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)))
    (hG : quaternionSize (thinQuaternionGradient ρ z) = κ*ρ z) (w : Fin m → Quaternion ℝ) :
    (κ*h/(h+ρ z)^2)*quaternionSize w ≤ quaternionForm (thinQuaternionHessian (thinLogBarrier h Q ρ) z) w := by
  have hpos : 0 < h+ρ z := by positivity
  have hcs := mul_le_mul_of_nonneg_left (quaternionForm_outer_le (thinQuaternionGradient ρ z) w)
    (show 0 ≤ 1/(h+ρ z)^2 by positivity)
  rw [hG] at hcs
  have he : κ/(h+ρ z)-(1/(h+ρ z)^2)*(κ*ρ z)=κ*h/(h+ρ z)^2 := by field_simp; ring
  rw [thinLogBarrier_hessian hh hρ hρ0 hD, quaternionForm_sub, quaternionForm_smul,
    quaternionForm_smul, quaternionForm_one]
  have he' := congrArg (fun c => c*quaternionSize w) he
  nlinarith only [hcs, he']

theorem thinLogBarrier_determinant {m : ℕ} (hm : 1 ≤ m) {h Q κ : ℝ}
    (hh : 0 < h) (hκ : 0 < κ) {ρ : ThinSpace m → ℝ} (hρ : ContDiff ℝ 2 ρ)
    {z : ThinSpace m} (hρ0 : 0 ≤ ρ z)
    (hD : thinQuaternionHessian ρ z = κ • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)))
    (hG : quaternionSize (thinQuaternionGradient ρ z) = κ*ρ z) :
    mooreDet m (thinQuaternionHessian (thinLogBarrier h Q ρ) z) = κ^m*h/(h+ρ z)^(m+1) := by
  have hpos : 0 < h+ρ z := by positivity
  rw [thinLogBarrier_hessian hh hρ hρ0 hD, sub_eq_add_neg, ← neg_smul,
    mooreDet_scalar_outer hm _ (div_pos hκ hpos).ne', hG]
  have he : κ/(h+ρ z)+(-(1/(h+ρ z)^2))*(κ*ρ z)=κ*h/(h+ρ z)^2 := by field_simp; ring
  rw [he, div_pow]
  have hp : (h+ρ z)^(m+1)=(h+ρ z)^(m-1)*(h+ρ z)^2 := by rw [← pow_add]; congr 1; omega
  have hk : κ^m=κ^(m-1)*κ := by rw [← pow_succ]; congr 1; omega
  rw [hp,hk]
  field_simp

end KakeyaSharp
