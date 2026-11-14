/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Trace.Estimate
public import KakeyaSharp.VariationalStructure

@[expose] public section

/-! Weighted source bounds for the actual variational supremum. The weight
may be discontinuous: only its nonnegativity, domination of the source,
and integrability of its critical power against the determinant are used. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp
open Set MeasureTheory Filter KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Topology

def thinWeightedConstant (m : ℕ) : ℝ :=
  (m : ℝ)/((m : ℝ)+1) * (thinTraceConstant m)^((m : ℝ)⁻¹)

theorem thinWeightedConstant_pos {m : ℕ} (hm : 1 ≤ m) : 0 < thinWeightedConstant m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  exact mul_pos (div_pos hm' (by positivity))
    (Real.rpow_pos_of_pos (thinTraceConstant_pos m) _)

theorem thin_scaled_young {m : ℕ} (hm : 1 ≤ m) {L U b : ℝ}
    (hL : 0 < L) (hU : 0 ≤ U) (hb : 0 ≤ b) :
    U*b ≤ (1/(((m : ℝ)+1)*L^m))*U^(m+1) +
      ((m : ℝ)/((m : ℝ)+1)*L)*b^(((m : ℝ)+1)/m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpq : ((m : ℝ)+1).HolderConjugate (((m : ℝ)+1)/m) := by
    simpa only [Real.conjExponent, add_sub_cancel_right] using
      Real.HolderConjugate.conjExponent (show (1 : ℝ) < (m : ℝ)+1 by linarith)
  have h := mul_le_mul_of_nonneg_left (Real.young_inequality_of_nonneg
    (div_nonneg hU hL.le) hb hpq) hL.le
  have hp : (U/L)^((m : ℝ)+1) = (U/L)^(m+1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.rpow_natCast (U/L) (m+1)
  rw [hp, div_pow, pow_succ] at h
  convert h using 1 <;> field_simp
  ring

theorem ThinAdmissibleAt.weighted_functional_bound_of_pos {m : ℕ} (hm : 1 ≤ m) {R H : ℝ}
    (hR : 0 < R) (hH : 0 < H) {o : ThinSpace m} {u φ ρ b : ThinSpace m → ℝ}
    (hu : ThinAdmissibleAt R o u)
    (hφ : ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 3 φ z)
    (hbound : ∀ z ∈ thinClosedBallAt R o, -H ≤ φ z ∧ φ z ≤ 0)
    (hpφ : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian φ z) a)
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hb : ∀ z ∈ thinBallAt R o, 0 ≤ b z)
    (hdom : ∀ z ∈ thinBallAt R o, ρ z ≤ b z*mooreDet m (thinQuaternionHessian φ z))
    (hi : IntegrableOn (fun z => (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z))
      (thinBallAt R o)) :
    thinFunctionalAt R o ρ u ≤ thinWeightedConstant m*H*
      ∫ z in thinBallAt R o, (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z) := by
  let L : ℝ := (thinTraceConstant m)^((m : ℝ)⁻¹)*H
  have hL : 0 < L := mul_pos (Real.rpow_pos_of_pos (thinTraceConstant_pos m) _) hH
  have hLm : L^m = thinTraceConstant m*H^m := by
    dsimp [L]
    rw [mul_pow, Real.rpow_inv_natCast_pow (thinTraceConstant_pos m).le (by omega)]
  have hc (z : ThinSpace m) (hz : z ∈ thinBallAt R o) : z ∈ thinClosedBallAt R o :=
    show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le
  have huc : ContinuousOn u (thinClosedBallAt R o) := fun z hz =>
    (hu.1 z hz).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (fun z => mooreDet m (thinQuaternionHessian φ z)) (thinClosedBallAt R o) := by
    intro z hz
    exact ((continuous_mooreDet m).continuousAt.comp
      (thinQuaternionHessian_continuousAt (hφ z hz))).continuousWithinAt
  have hip : IntegrableOn (fun z => (-u z)^(m+1)*mooreDet m (thinQuaternionHessian φ z))
      (thinBallAt R o) :=
    (((huc.neg.pow _).mul hdc).integrableOn_compact (thinClosedBallAt_compact hR.le o)).mono_set hc
  let A : ℝ := 1/(((m : ℝ)+1)*L^m)
  let C : ℝ := (m : ℝ)/((m : ℝ)+1)*L
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsource : (∫ z in thinBallAt R o, (-u z)*ρ z) ≤
      A*(∫ z in thinBallAt R o, (-u z)^(m+1)*mooreDet m (thinQuaternionHessian φ z)) +
      C*(∫ z in thinBallAt R o, (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hip.const_mul A) (hi.const_mul C)]
    apply setIntegral_mono_on (hu.source_integrableOn hR hρ)
      ((hip.const_mul A).add (hi.const_mul C)) (thinBallAt_measurable R o)
    intro z hz
    have hU : 0 ≤ -u z := neg_nonneg.mpr (hu.nonpos hm hR z (hc z hz))
    have hd : 0 ≤ mooreDet m (thinQuaternionHessian φ z) :=
      thinDet_nonneg ((hφ z (hc z hz)).of_le (by norm_num)) (hpφ z hz)
    have h1 := mul_le_mul_of_nonneg_left (hdom z hz) hU
    have h2 := mul_le_mul_of_nonneg_right (thin_scaled_young hm hL hU (hb z hz)) hd
    dsimp [A,C] at *
    nlinarith
  have htrace := mul_le_mul_of_nonneg_left (hu.trace_bound hm hR hH.le hφ hbound hpφ) hA
  have he : A*(thinTraceConstant m*H^m*determinantEnergyAt R o u) =
      determinantEnergyAt R o u/((m : ℝ)+1) := by
    rw [← hLm]
    dsimp [A]
    field_simp
  rw [he] at htrace
  have hC : C = thinWeightedConstant m*H := by dsimp [C,L,thinWeightedConstant]; ring
  rw [hC] at hsource
  unfold thinFunctionalAt
  linarith

theorem ThinAdmissibleAt.weighted_functional_bound {m : ℕ} (hm : 1 ≤ m) {R H : ℝ}
    (hR : 0 < R) (hH : 0 ≤ H) {o : ThinSpace m} {u φ ρ b : ThinSpace m → ℝ}
    (hu : ThinAdmissibleAt R o u)
    (hφ : ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 3 φ z)
    (hbound : ∀ z ∈ thinClosedBallAt R o, -H ≤ φ z ∧ φ z ≤ 0)
    (hpφ : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian φ z) a)
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hb : ∀ z ∈ thinBallAt R o, 0 ≤ b z)
    (hdom : ∀ z ∈ thinBallAt R o, ρ z ≤ b z*mooreDet m (thinQuaternionHessian φ z))
    (hi : IntegrableOn (fun z => (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z))
      (thinBallAt R o)) :
    thinFunctionalAt R o ρ u ≤ thinWeightedConstant m*H*
      ∫ z in thinBallAt R o, (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, thinFunctionalAt R o ρ u ≤ thinWeightedConstant m*(H+ε)*
      ∫ z in thinBallAt R o, (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hu.weighted_functional_bound_of_pos hm hR (add_pos_of_nonneg_of_pos hH hε) hφ
      (fun z hz => ⟨by have hh := (hbound z hz).1; change 0 < ε at hε; linarith,
        (hbound z hz).2⟩) hpφ hρ hb hdom hi
  have ht : Tendsto (fun ε : ℝ => thinWeightedConstant m*(H+ε)*
      ∫ z in thinBallAt R o, (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z))
      (𝓝[>] 0) (𝓝 (thinWeightedConstant m*H*
        ∫ z in thinBallAt R o, (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z))) := by
    have hcont : Continuous (fun ε : ℝ => thinWeightedConstant m*(H+ε)*
        ∫ z in thinBallAt R o, (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z)) := by
      fun_prop
    simpa only [add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht he

theorem thinValueRealAt_weighted_bound {m : ℕ} (hm : 1 ≤ m) {R H : ℝ}
    (hR : 0 < R) (hH : 0 ≤ H) (o : ThinSpace m) {φ ρ b : ThinSpace m → ℝ}
    (hφ : ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 3 φ z)
    (hbound : ∀ z ∈ thinClosedBallAt R o, -H ≤ φ z ∧ φ z ≤ 0)
    (hpφ : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian φ z) a)
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hb : ∀ z ∈ thinBallAt R o, 0 ≤ b z)
    (hdom : ∀ z ∈ thinBallAt R o, ρ z ≤ b z*mooreDet m (thinQuaternionHessian φ z))
    (hi : IntegrableOn (fun z => (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z))
      (thinBallAt R o)) :
    thinValueRealAt R o ρ ≤ thinWeightedConstant m*H*
      ∫ z in thinBallAt R o, (b z)^(((m : ℝ)+1)/m)*mooreDet m (thinQuaternionHessian φ z) := by
  apply thinValueRealAt_le hm hR o hρ
  intro u hu
  exact hu.weighted_functional_bound hm hR hH hφ hbound hpφ hρ hb hdom hi

end KakeyaSharp
