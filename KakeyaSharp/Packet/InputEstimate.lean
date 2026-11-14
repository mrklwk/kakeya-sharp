/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.InputIntegration
public import KakeyaSharp.Packet.DirectionIntegral

@[expose] public section

/-! The single-log input estimate for the actual normalized Kakeya packet
family. No trace, domination, overlap or normal-integral estimate is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set MeasureTheory KakeyaSharp.Moore

def inputExponent (m : ℕ) : ℝ := ((m : ℝ)+1)/m

theorem inputExponent_ge_one {m : ℕ} (hm : 1 ≤ m) : 1 ≤ inputExponent m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold inputExponent
  exact (le_div_iff₀ hm').mpr (by linarith)

def inputIntegralConstant (m : ℕ) (A : ℝ) : ℝ :=
  ((8 : ℝ)^m*normalMass m)*
    ((inputDensityConstant m A)^(inputExponent m)*directionIntegralConstant m (inputExponent m))

def inputEstimateConstant (m : ℕ) (A R : ℝ) : ℝ :=
  (thinWeightedConstant m*inputLogConstant R)*inputIntegralConstant m A

theorem inputIntegralConstant_pos {m : ℕ} {A : ℝ} (hA : 0 ≤ A) :
    0 < inputIntegralConstant m A := by
  unfold inputIntegralConstant
  exact mul_pos (mul_pos (by positivity) (normalMass_pos m))
    (mul_pos (Real.rpow_pos_of_pos (inputDensityConstant_pos m hA) _)
      (directionIntegralConstant_pos _ _))

theorem inputEstimateConstant_pos {m : ℕ} (hm : 1 ≤ m) {A : ℝ} (hA : 0 ≤ A) (R : ℝ) :
    0 < inputEstimateConstant m A R :=
  mul_pos (mul_pos (thinWeightedConstant_pos hm) (inputLogConstant_pos R))
    (inputIntegralConstant_pos hA)

theorem inputIntegralConstant_nonneg {m : ℕ} {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ inputIntegralConstant m A := by
  unfold inputIntegralConstant
  exact mul_nonneg (mul_nonneg (by positivity) (normalMass_nonneg m))
    (mul_nonneg (Real.rpow_nonneg (inputDensityConstant_pos m hA).le _)
      (directionIntegralConstant_pos _ _).le)

theorem inputEstimateConstant_nonneg {m : ℕ} (hm : 1 ≤ m) {A : ℝ} (hA : 0 ≤ A) (R : ℝ) :
    0 ≤ inputEstimateConstant m A R :=
  mul_nonneg (mul_nonneg (thinWeightedConstant_pos hm).le (inputLogConstant_pos R).le)
    (inputIntegralConstant_nonneg hA)

theorem input_direction_weight_integrable {m N : ℕ} (hm : 1 ≤ m) {δ A : ℝ}
    (hδ : 0 < δ) (hA : 0 ≤ A) (v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (hsep : ∀ i j, i ≠ j →
      δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j))) :
    Integrable (fun α => (inputDensityConstant m A*directionWeight δ v weights α)^(inputExponent m)) := by
  have he : (fun α => (inputDensityConstant m A*directionWeight δ v weights α)^(inputExponent m)) =
      (fun α => (inputDensityConstant m A)^(inputExponent m)*
        (directionWeight δ v weights α)^(inputExponent m)) := by
    funext α
    exact Real.mul_rpow (inputDensityConstant_pos m hA).le (directionWeight_nonneg δ v hw α)
  rw [he]
  exact (directionWeight_rpow_integrable hδ (inputExponent_ge_one hm) v hw hsep).const_mul _

theorem input_direction_weight_measurable {m N : ℕ} (hm : 1 ≤ m)
    (δ A : ℝ) (v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    Measurable (fun α => (inputDensityConstant m A*directionWeight δ v weights α)^(inputExponent m)) :=
  (Real.continuous_rpow_const (le_trans (by norm_num) (inputExponent_ge_one hm))).measurable.comp
    (measurable_const.mul (directionWeight_measurable δ v weights))

theorem kakeya_input_weighted_integrable {m N : ℕ} (hm : 1 ≤ m) {δ A : ℝ}
    (hδ : 0 < δ) (hA : 0 ≤ A) (v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (hsep : ∀ i j, i ≠ j →
      δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j)))
    {p : Space 3} (hp : (p 1)^2+(p 2)^2=1) :
    Integrable (fun z => (inputDensityConstant m A*directionWeight δ v weights (inputAlpha p z))^
      (inputExponent m)*inputKernel m (δ^4) (p 1) (p 2) z) :=
  input_weighted_integrable hm (pow_pos hδ 4) hp
    (input_direction_weight_measurable hm δ A v weights)
    (input_direction_weight_integrable hm hδ hA v hw hsep)
    (fun α => Real.rpow_nonneg
      (mul_nonneg (inputDensityConstant_pos m hA).le (directionWeight_nonneg δ v hw α)) _)

theorem kakeya_input_weighted_integral_le {m N : ℕ} (hm : 1 ≤ m) {δ A R : ℝ}
    (hδ : 0 < δ) (hA : 0 ≤ A) (v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (hsep : ∀ i j, i ≠ j →
      δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j)))
    {p : Space 3} (hp : (p 1)^2+(p 2)^2=1) :
    (∫ z in thinBallAt R 0,
      (inputDensityConstant m A*directionWeight δ v weights (inputAlpha p z))^
        (inputExponent m)*inputKernel m (δ^4) (p 1) (p 2) z) ≤
      inputIntegralConstant m A*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  have hnonneg (α : Space m) : 0 ≤
      (inputDensityConstant m A*directionWeight δ v weights α)^(inputExponent m) :=
    Real.rpow_nonneg (mul_nonneg (inputDensityConstant_pos m hA).le (directionWeight_nonneg δ v hw α)) _
  have h1 := setIntegral_le_integral (s := thinBallAt R 0)
    (kakeya_input_weighted_integrable hm hδ hA v hw hsep hp)
    (ae_of_all _ (fun z => mul_nonneg (hnonneg _) (inputKernel_nonneg m (pow_pos hδ 4) _ _ z)))
  have h2 := input_weighted_integral_le hm (pow_pos hδ 4) hp
    (input_direction_weight_measurable hm δ A v weights)
    (input_direction_weight_integrable hm hδ hA v hw hsep) hnonneg
  have he : (fun α => (inputDensityConstant m A*directionWeight δ v weights α)^(inputExponent m)) =
      (fun α => (inputDensityConstant m A)^(inputExponent m)*
        (directionWeight δ v weights α)^(inputExponent m)) := by
    funext α
    exact Real.mul_rpow (inputDensityConstant_pos m hA).le (directionWeight_nonneg δ v hw α)
  rw [he, integral_const_mul] at h2
  have h3 := mul_le_mul_of_nonneg_left
    (directionWeight_rpow_integral_le hm hδ (inputExponent_ge_one hm) v hw hsep)
    (mul_nonneg (mul_nonneg (by positivity : 0 ≤ (8 : ℝ)^m) (normalMass_nonneg m))
      (Real.rpow_nonneg (inputDensityConstant_pos m hA).le (inputExponent m)))
  apply (h1.trans h2).trans
  simpa only [inputIntegralConstant, mul_assoc] using h3

/-- The actual packet supremum at time zero and every unit transverse orientation.
The constant depends only on dimension, the intercept bound and the fixed ball radius. -/
theorem kakeyaPacketFamily_input_estimate {m N : ℕ} (hm : 1 ≤ m) {δ A R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A) (hR : 0 < R)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (ha : ∀ l, (∑ j, (a l j)^2) ≤ A)
    (hsep : ∀ i j, i ≠ j →
      δ ≤ dist (WithLp.toLp 2 (v i) : Space m) (WithLp.toLp 2 (v j)))
    {p : Space 3} (ht : p 0=0) (hp : (p 1)^2+(p 2)^2=1) :
    thinValueRealAt R 0 (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) p) ≤
      inputEstimateConstant m A R*Real.log (2/δ)*δ^m*(∑ l, (weights l)^(inputExponent m)) := by
  have hpd : p ∈ packetDomain m := by
    change (p 0-1)^2 < 16 ∧ 0 < radius (p,(0 : ThinSpace m)) ∧ radius (p,(0 : ThinSpace m)) < 4
    rw [ht, radius_eq_one_of_unit hp]
    norm_num
  have hμ : ContinuousOn (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) p)
      (thinClosedBallAt R 0) :=
    (kakeyaPacketFamily_density_continuous hδ a v weights).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun z _ => ⟨hpd,mem_univ z⟩)
  have hbound := inputBarrier_value_le_log hm hδ hδ1 hR hp hμ
    (w := fun z => inputDensityConstant m A*directionWeight δ v weights (inputAlpha p z))
    (fun z _ => mul_nonneg (inputDensityConstant_pos m hA).le (directionWeight_nonneg δ v hw _))
    (fun z _ => by
      have hd := kakeyaPacketFamily_input_domination hm (R := R) hδ hδ1 hA a v hw ha ht hp z
      rw [inputBarrier_determinant hm (pow_pos hδ 4) hp] at hd
      exact hd)
    (kakeya_input_weighted_integrable hm hδ hA v hw hsep hp).integrableOn
  have hlog : 0 ≤ Real.log (2/δ) := Real.log_nonneg (by
    apply (le_div_iff₀ hδ).mpr
    linarith)
  have hmult := mul_le_mul_of_nonneg_left
    (kakeya_input_weighted_integral_le hm (R := R) hδ hA v hw hsep hp)
    (mul_nonneg (mul_nonneg (thinWeightedConstant_pos hm).le (inputLogConstant_pos R).le) hlog)
  exact hbound.trans (hmult.trans_eq (by unfold inputEstimateConstant; ring))

end KakeyaSharp.Packet
