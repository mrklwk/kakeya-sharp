/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.OutputGeometry

@[expose] public section

/-! A weighted tube slice controls the actual packet value. The scale
factor delta^2 is exactly the later change of time variable. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory OAI.Analysis.PDE.Concentration

def outputSliceConstant (m : ℕ) : ℝ :=
  outputLowerConstant m (1/100) (1/1000)/coverMass m

theorem outputSliceConstant_pos (m : ℕ) : 0 < outputSliceConstant m :=
  div_pos (outputLowerConstant_pos m (by norm_num) (by norm_num)) (coverMass_pos m)

theorem kakeyaPacketFamily_output_slice_lower {m N : ℕ} (hm : 1 ≤ m)
    {δ A t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (ha : ∀ l, (∑ j, (a l j)^2) ≤ A) (hv : ∀ l, (∑ j, (v l j)^2) ≤ 1/16)
    (ht : t ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    outputSliceConstant m*Real.log (2/δ)*
        (∫ x, (sliceOverlap δ a v weights t x)^(inputExponent m)) ≤
      δ^2*thinValueRealAt (propagationOuterRadius A (1/16)) 0
        (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights))
          (cylinderPoint (1+δ^2*t) (δ^4) θ)) := by
  obtain ⟨J,b,hb,hsep,hcover⟩ := compact_finite_separated_net
    (isCompact_closedBall (0 : Space m) (sliceSupportRadius A))
    (by positivity : 0 < δ/32)
  have hcov := sliceOverlap_integral_le_cover (by omega : 1 ≤ m) hδ
    (inputExponent_ge_one (m := m) (by omega)) a v hw t b
    (fun x hx => hcover x (sliceOverlap_support hδ1 hA a v weights ha hv ht hx))
  have htime : ((cylinderPoint (1+δ^2*t) (δ^4) θ) 0-1)^2 ≤ (δ^2)^2 := by
    have ht2 : t^2 ≤ 1 := pow_le_one₀ ht.1 ht.2
    have hmul := mul_le_mul_of_nonneg_left ht2 (sq_nonneg (δ^2))
    simpa [cylinderPoint,cylinderRadial,cylinderAxis,EuclideanSpace.basisFun_apply,mul_pow] using hmul
  have hlower := kakeyaPacketFamily_localized_output_lower hm hδ hδ1
    (propagationOuterRadius_pos A (1/16)) a v hw
    (fun _ : Fin J => outputBallRadius δ) (fun _ => outputThickness δ)
    (fun j => outputCenter δ (b j)) (fun j => nearbyPackets δ a v t (b j))
    (fun _ => by unfold outputBallRadius; positivity)
    (fun _ => by unfold outputThickness; positivity)
    (fun _ => by
      unfold outputThickness outputBallRadius
      nlinarith [mul_le_mul_of_nonneg_left hδ1 (pow_nonneg hδ.le 3)])
    (fun _ => by unfold outputBallRadius; nlinarith [pow_pos hδ 3])
    (fun _ => by unfold outputThickness; nlinarith [pow_pos hδ 4])
    (fun _ => rfl) (fun j => output_ball_in_outer hδ hδ1 hA (hb j))
    (output_balls_disjoint hδ b hsep)
    (output_parameter_radius hδ t θ) htime (fun _ l _ => hv l) (by
      intro j l hl
      have hd : dist (b j) (graphAxis (a l) (v l) t) ≤ δ/16 :=
        (Finset.mem_filter.mp hl).2
      rw [outputAxis_at_time]
      change ‖δ^2 • b j-δ^2 • graphAxis (a l) (v l) t‖ ≤ δ^3/8
      rw [← smul_sub,norm_smul,Real.norm_of_nonneg (sq_nonneg δ),← dist_eq_norm]
      nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg δ),pow_pos hδ 3])
  have he (j : Fin J) :
      thinLowerConstant m*(outputBallRadius δ)^m*(outputThickness δ)^(2*m+2)*
        (outputDensityScale m δ*(∑ l ∈ nearbyPackets δ a v t (b j), weights l))^
          (((m : ℝ)+1)/m)*Real.log (outputBallRadius δ/outputThickness δ) =
      outputLowerConstant m (1/100) (1/1000)*δ^((m : ℝ)-2)*Real.log (10/δ)*
        (coverWeight δ a v weights t (b j))^(inputExponent m) := by
    change thinLowerConstant m*((1/100)*δ^3)^m*((1/1000)*δ^4)^(2*m+2)*
      (outputDensityScale m δ*coverWeight δ a v weights t (b j))^(inputExponent m)*
        Real.log (((1/100)*δ^3)/((1/1000)*δ^4)) = _
    rw [output_lower_scaling_real hm hδ (coverWeight_nonneg δ a v hw t (b j))]
    have hratio : (1/100 : ℝ)/((1/1000)*δ)=10/δ := by field_simp; ring
    rw [hratio]
    ring
  simp_rw [he] at hlower
  rw [← Finset.mul_sum] at hlower
  have hlog : Real.log (2/δ) ≤ Real.log (10/δ) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) hδ.le)
  have hlog0 : 0 ≤ Real.log (2/δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hK : 0 < outputLowerConstant m (1/100) (1/1000) :=
    outputLowerConstant_pos m (by norm_num) (by norm_num)
  have hS : 0 ≤ ∑ j, (coverWeight δ a v weights t (b j))^(inputExponent m) :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (coverWeight_nonneg δ a v hw t (b j)) _)
  have hlow :
      outputLowerConstant m (1/100) (1/1000)*δ^((m : ℝ)-2)*Real.log (2/δ)*
        (∑ j, (coverWeight δ a v weights t (b j))^(inputExponent m)) ≤
      thinValueRealAt (propagationOuterRadius A (1/16)) 0
        (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights))
          (cylinderPoint (1+δ^2*t) (δ^4) θ)) := by
    apply le_trans _ hlower
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog (mul_nonneg hK.le (Real.rpow_nonneg hδ.le _))) hS
  have hp : δ^2*δ^((m : ℝ)-2)=δ^m := by
    rw [← Real.rpow_natCast δ 2,← Real.rpow_add hδ]
    convert Real.rpow_natCast δ m using 1
    congr 1
    push_cast
    ring
  calc
    _ ≤ outputSliceConstant m*Real.log (2/δ)*
        (coverMass m*δ^m*(∑ j, (coverWeight δ a v weights t (b j))^(inputExponent m))) :=
      mul_le_mul_of_nonneg_left hcov (mul_nonneg (outputSliceConstant_pos m).le hlog0)
    _ = δ^2*(outputLowerConstant m (1/100) (1/1000)*δ^((m : ℝ)-2)*Real.log (2/δ)*
        (∑ j, (coverWeight δ a v weights t (b j))^(inputExponent m))) := by
      rw [← hp]
      unfold outputSliceConstant
      field_simp [(coverMass_pos m).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (sq_nonneg δ)

end KakeyaSharp.Packet
