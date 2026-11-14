/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.OutputSlice
public import KakeyaSharp.Packet.TubeSliceIntegral
public import KakeyaSharp.Propagation.ContinuousTrace

@[expose] public section

/-! The normalized weighted tube bound in dimensions at least two.
The output lower bound cancels one logarithm from cylinder propagation. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set MeasureTheory OAI.Analysis.PDE.Concentration

def normalizedTubeMoment {m N : ℕ} (δ : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, sliceIntegral δ a v weights t

theorem kakeyaPacketFamily_output_integral_lower {m N : ℕ} (hm : 1 ≤ m)
    {δ A : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hA : 0 ≤ A)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (ha : ∀ l, (∑ j, (a l j)^2) ≤ A) (hv : ∀ l, (∑ j, (v l j)^2) ≤ 1/16) :
    2*Real.pi*outputSliceConstant m*Real.log (2/δ)*normalizedTubeMoment δ a v weights ≤
      ∫ t in (1 : ℝ)..2, ∫ θ in (0 : ℝ)..(2*Real.pi),
        thinValueRealAt (propagationOuterRadius A (1/16)) 0
          (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights))
            (cylinderPoint t (δ^4) θ)) := by
  let R := propagationOuterRadius A (1/16)
  let f : Space 3 → ℝ := fun p => thinValueRealAt R 0
    (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) p)
  let F : ℝ → ℝ := fun t => cylinderAngularAverage f t (δ^4)
  have hρ : 0 < δ^4 := pow_pos hδ 4
  have hρ1 : δ^4 < 1 := pow_lt_one₀ hδ.le hδ1 (by norm_num)
  have htrace := Propagation.continuous_cylinder_trace hρ hρ1
    (propagationPacketDomain_isOpen m) (cylinderCompact_subset_propagationPacketDomain m hρ)
    (kakeyaPacketFamily_propagation_value_continuous (by omega : 1 ≤ m) hδ
      (propagationOuterRadius_pos A (1/16)) a v weights)
  have hFc : ContinuousOn F (Icc (1 : ℝ) 2) := htrace.1
  have hFi : IntervalIntegrable F volume 1 2 := hFc.intervalIntegrable_of_Icc (by norm_num)
  have hFn (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) : 0 ≤ F t := by
    apply cylinderAngularAverage_nonneg
    intro θ _
    exact kakeyaPacketFamily_propagation_value_nonneg (by omega) hδ
      (propagationOuterRadius_pos A (1/16)) a v weights
      (cylinderCompact_subset_propagationPacketDomain m hρ
        (Propagation.tracePoint_mem_compact hρ hρ1 ht θ))
  have hwindow {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1+δ^2*t ∈ Icc (1 : ℝ) 2 := by
    have hd : δ^2 ≤ 1 := pow_le_one₀ hδ.le hδ1.le
    constructor
    · nlinarith [mul_nonneg (sq_nonneg δ) ht.1]
    · nlinarith [mul_le_mul_of_nonneg_left ht.2 (sq_nonneg δ)]
  have hcomp : ContinuousOn (fun t => F (1+δ^2*t)) (Icc (0 : ℝ) 1) :=
    hFc.comp (by fun_prop) (fun _ ht => hwindow ht)
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      2*Real.pi*outputSliceConstant m*Real.log (2/δ)*sliceIntegral δ a v weights t ≤
        δ^2*F (1+δ^2*t) := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) (by positivity : (0 : ℝ) ≤ 2*Real.pi)
      (intervalIntegrable_const (c := outputSliceConstant m*Real.log (2/δ)*
        sliceIntegral δ a v weights t))
      (((htrace.2 _ (hwindow ht)).intervalIntegrable 0 (2*Real.pi)).const_mul (δ^2))
      (fun θ _ => kakeyaPacketFamily_output_slice_lower hm hδ hδ1.le hA a v hw ha hv ht θ)
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,
      intervalIntegral.integral_const_mul] at hi
    exact (by convert hi using 1 <;> first | rfl | ring)
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    ((sliceIntegral_intervalIntegrable (by omega : 1 ≤ m) hδ a v hw).const_mul
      (2*Real.pi*outputSliceConstant m*Real.log (2/δ)))
    ((hcomp.intervalIntegrable_of_Icc (by norm_num)).const_mul (δ^2)) hs
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hi
  have he := intervalIntegral.smul_integral_comp_add_mul F (a := 0) (b := 1) (δ^2) 1
  simp only [smul_eq_mul,mul_zero,mul_one,add_zero] at he
  rw [he] at hi
  have hsub := intervalIntegral.integral_mono_interval (le_refl (1 : ℝ))
    (show 1 ≤ 1+δ^2 by nlinarith [sq_nonneg δ])
    (show 1+δ^2 ≤ 2 by nlinarith [pow_le_one₀ hδ.le hδ1.le (n := 2)])
    ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ (fun t ht => hFn t ⟨ht.1.le,ht.2⟩))) hFi
  exact hi.trans hsub

/-- For bounded intercepts, small slopes, and delta-separated directions,
the q-th moment of the weighted overlap of radius-delta/64 graph tubes
has the single logarithm log(2/delta), with q=(m+1)/m. -/
theorem exists_normalizedTube_constant {m : ℕ} (hm : 1 ≤ m) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      ∀ (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ),
      (∀ l, 0 ≤ weights l) → (∀ l, (∑ j, (a l j)^2) ≤ A) →
      (∀ l, (∑ j, (v l j)^2) ≤ 1/16) →
      (∀ i j, i ≠ j → δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) →
      normalizedTubeMoment δ a v weights ≤
        C*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  obtain ⟨C,hC,hupper⟩ := exists_kakeyaPacketFamily_output_upper_constant
    (by omega : 1 ≤ m) hA (1/16)
  have hbase : 0 < 2*Real.pi*outputSliceConstant m :=
    mul_pos (by positivity) (outputSliceConstant_pos m)
  refine ⟨C/(2*Real.pi*outputSliceConstant m),div_pos hC hbase,?_⟩
  intro N δ hδ hδ1 a v weights hw ha hv hsep
  have hL : 0 < Real.log (2/δ) :=
    Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have h := (kakeyaPacketFamily_output_integral_lower hm hδ hδ1 hA a v hw ha hv).trans
    (hupper N δ hδ hδ1 a v weights hw ha hv hsep)
  have he :
      C*(Real.log (2/δ))^2*δ^m*(∑ l, (weights l)^(inputExponent m)) =
        (2*Real.pi*outputSliceConstant m*Real.log (2/δ))*
          (C/(2*Real.pi*outputSliceConstant m)*Real.log (2/δ)*δ^m*
            (∑ l, (weights l)^(inputExponent m))) := by
    field_simp [(outputSliceConstant_pos m).ne']
  rw [he] at h
  exact (mul_le_mul_iff_right₀ (mul_pos hbase hL)).mp (by simpa only [mul_comm] using h)

end KakeyaSharp.Packet
