/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.PropagationDomain
public import KakeyaSharp.Packet.InputEstimate

@[expose] public section

/-! Propagation of the actual weighted Kakeya packet value from the separated
input slice to every smaller positive cylinder radius. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open MeasureTheory Set OAI.Analysis.PDE.Concentration

/-- The constant is independent of scale, packet count, coefficients and the
smaller cylinder radius. The two logarithms come from input and propagation. -/
theorem exists_kakeyaPacketFamily_propagation_constant {m : ℕ} (hm : 1 ≤ m)
    {A : ℝ} (hA : 0 ≤ A) (V : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (δ ρ : ℝ), 0 < δ → δ ≤ 1 → 0 < ρ → ρ < 1 →
    ∀ (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ),
    (∀ l, 0 ≤ weights l) → (∀ l, (∑ j, (a l j)^2) ≤ A) →
    (∀ l, (∑ j, (v l j)^2) ≤ V) →
    (∀ i j, i ≠ j → δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) →
    (∫ t in (1 : ℝ)..2, ∫ θ in (0 : ℝ)..(2*Real.pi),
      thinValueRealAt (propagationOuterRadius A V) 0
        (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) (cylinderPoint t ρ θ))) ≤
      C*(1+|Real.log ρ|)*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  obtain ⟨C,hC,hprop⟩ := Propagation.exists_weak_singleLog_cylinder_constant
  let R := propagationOuterRadius A V
  have hR : 0 < R := propagationOuterRadius_pos A V
  refine ⟨C*inputEstimateConstant m A R,
    mul_pos hC (inputEstimateConstant_pos hm hA R),?_⟩
  intro N δ ρ hδ hδ1 hρ hρ1 a v weights hw ha hv hsep
  let f : Space 3 → ℝ := fun p => thinValueRealAt R 0
    (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) p)
  have h := hprop ρ hρ hρ1 (propagationPacketDomain m)
    (propagationPacketDomain_isOpen m) (cylinderCompact_subset_propagationPacketDomain m hρ)
    f (kakeyaPacketFamily_propagation_value_continuous hm hδ hR a v weights)
    (kakeyaPacketFamily_propagation_weakSuperharmonic hm hδ hδ1 a v hw ha hv)
    (fun p hp => kakeyaPacketFamily_propagation_value_nonneg hm hδ hR a v weights hp) 0
  have ht : (cylinderPoint 0 1 0) 0=0 := by
    simp [cylinderPoint,cylinderRadial,cylinderAxis,EuclideanSpace.basisFun_apply]
  have hp : ((cylinderPoint 0 1 0) 1)^2+((cylinderPoint 0 1 0) 2)^2=1 := by
    norm_num [cylinderPoint,cylinderRadial,cylinderAxis,EuclideanSpace.basisFun_apply]
  have hi := kakeyaPacketFamily_input_estimate hm hδ hδ1 hA hR a v hw ha hsep ht hp
  have hmult := mul_le_mul_of_nonneg_left hi
    (mul_nonneg hC.le (by positivity : 0 ≤ 1+|Real.log ρ|))
  exact h.trans (hmult.trans_eq (by ring))

theorem propagationLog_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1+|Real.log (δ^4)| ≤ 6*Real.log (2/δ) := by
  have hl : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  rw [Real.log_pow,Real.log_div (by norm_num) hδ.ne']
  norm_num only [Nat.cast_ofNat]
  rw [abs_of_nonpos (by linarith : (4 : ℝ)*Real.log δ ≤ 0)]
  linarith [Real.log_two_gt_d9]

/-- The exact packet output radius is h = delta^4. Propagation to that
radius gives the squared-log upper bound used in the final cancellation. -/
theorem exists_kakeyaPacketFamily_output_upper_constant {m : ℕ} (hm : 1 ≤ m)
    {A : ℝ} (hA : 0 ≤ A) (V : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
    ∀ (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ),
    (∀ l, 0 ≤ weights l) → (∀ l, (∑ j, (a l j)^2) ≤ A) →
    (∀ l, (∑ j, (v l j)^2) ≤ V) →
    (∀ i j, i ≠ j → δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) →
    (∫ t in (1 : ℝ)..2, ∫ θ in (0 : ℝ)..(2*Real.pi),
      thinValueRealAt (propagationOuterRadius A V) 0
        (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) (cylinderPoint t (δ^4) θ))) ≤
      C*(Real.log (2/δ))^2*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  obtain ⟨C,hC,hprop⟩ := exists_kakeyaPacketFamily_propagation_constant hm hA V
  refine ⟨6*C,mul_pos (by norm_num) hC,?_⟩
  intro N δ hδ hδ1 a v weights hw ha hv hsep
  have h := hprop N δ (δ^4) hδ hδ1.le (pow_pos hδ 4)
    (pow_lt_one₀ hδ.le hδ1 (by norm_num)) a v weights hw ha hv hsep
  have hl : 0 ≤ Real.log (2/δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hs : 0 ≤ ∑ l, (weights l)^(inputExponent m) :=
    Finset.sum_nonneg (fun l _ => Real.rpow_nonneg (hw l) _)
  have hmult := mul_le_mul_of_nonneg_right (propagationLog_le hδ hδ1.le)
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le hl) (pow_nonneg hδ.le m)) hs)
  apply h.trans
  nlinarith [hmult]

end KakeyaSharp.Packet
