/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.OutputLocalization
public import KakeyaSharp.Packet.Propagation

@[expose] public section

/-! Exact scale bookkeeping for the localized logarithmic output bound. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet

def outputDensityConstant (m : ℕ) : ℝ :=
  (5 : ℝ)^(-(m : ℝ)/2)/cutoffMass m standardCutoff

theorem outputDensityConstant_pos (m : ℕ) : 0 < outputDensityConstant m :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (standardCutoff_mass_pos m)

theorem outputDensityScale_eq (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    outputDensityScale m δ = outputDensityConstant m*δ^(-(10*(m : ℝ))) := by
  have hb : 5*(δ^4)^2*(δ^2)^2=5*δ^12 := by ring
  have hd : (δ^4)^m=δ^((4 : ℝ)*(m : ℝ)) := by
    rw [Real.rpow_mul_natCast hδ.le]
    norm_cast
  unfold outputDensityScale
  rw [hb,Real.mul_rpow (by norm_num) (pow_nonneg hδ.le 12),
    ← Real.rpow_natCast_mul hδ.le,hd]
  norm_num only [Nat.cast_ofNat]
  calc
    _ = outputDensityConstant m *
        (δ^((12 : ℝ)*(-(m : ℝ)/2))/δ^((4 : ℝ)*(m : ℝ))) := by
      unfold outputDensityConstant
      ring
    _ = _ := by
      rw [← Real.rpow_sub hδ]
      congr 2
      ring

def outputLowerConstant (m : ℕ) (r₀ ε₀ : ℝ) : ℝ :=
  thinLowerConstant m*r₀^m*ε₀^(2*m+2)*(outputDensityConstant m)^(inputExponent m)

theorem outputLowerConstant_pos (m : ℕ) {r₀ ε₀ : ℝ} (hr : 0 < r₀) (hε : 0 < ε₀) :
    0 < outputLowerConstant m r₀ ε₀ := by
  unfold outputLowerConstant
  exact mul_pos (mul_pos (mul_pos (thinLowerConstant_pos m) (pow_pos hr m))
    (pow_pos hε _)) (Real.rpow_pos_of_pos (outputDensityConstant_pos m) _)

theorem output_delta_power {m : ℕ} (hm : 2 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    δ^(3*m)*δ^(4*(2*m+2))*(δ^(-(10*(m : ℝ))))^(inputExponent m) = δ^(m-2) := by
  rw [← Real.rpow_mul hδ.le,← Real.rpow_natCast δ (3*m),
    ← Real.rpow_natCast δ (4*(2*m+2)),← Real.rpow_add hδ,← Real.rpow_add hδ,
    ← Real.rpow_natCast δ (m-2)]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Nat.cast_sub hm]
  unfold inputExponent
  push_cast
  field_simp
  ring

/-- The spatial radius is r0*delta^3, the transverse radius epsilon0*delta^4,
and the density scale is delta^(-10m). Their exact combined power is delta^(m-2). -/
theorem output_lower_scaling {m : ℕ} (hm : 2 ≤ m) {δ r₀ ε₀ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) :
    thinLowerConstant m*(r₀*δ^3)^m*(ε₀*δ^4)^(2*m+2)*
      (outputDensityScale m δ*M)^(inputExponent m)*
        Real.log ((r₀*δ^3)/(ε₀*δ^4)) =
      outputLowerConstant m r₀ ε₀*δ^(m-2)*M^(inputExponent m)*Real.log (r₀/(ε₀*δ)) := by
  have hlog : (r₀*δ^3)/(ε₀*δ^4)=r₀/(ε₀*δ) := by
    by_cases hε : ε₀=0
    · simp [hε]
    · field_simp
  rw [outputDensityScale_eq m hδ,Real.mul_rpow
    (mul_nonneg (outputDensityConstant_pos m).le (Real.rpow_nonneg hδ.le _)) hM,
    Real.mul_rpow (outputDensityConstant_pos m).le (Real.rpow_nonneg hδ.le _),
    mul_pow,mul_pow,← pow_mul,← pow_mul,hlog]
  have hp := output_delta_power hm hδ
  unfold outputLowerConstant
  calc
    _ = (thinLowerConstant m*r₀^m*ε₀^(2*m+2)*(outputDensityConstant m)^(inputExponent m))*
        (δ^(3*m)*δ^(4*(2*m+2))*(δ^(-(10*(m : ℝ))))^(inputExponent m))*
        M^(inputExponent m)*Real.log (r₀/(ε₀*δ)) := by ring
    _ = _ := by rw [hp]

/-- The real exponent is essential in dimension m=1, where the power is -1. -/
theorem output_delta_power_real {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    δ^(3*m)*δ^(4*(2*m+2))*(δ^(-(10*(m : ℝ))))^(inputExponent m) = δ^((m : ℝ)-2) := by
  rw [← Real.rpow_mul hδ.le,← Real.rpow_natCast δ (3*m),
    ← Real.rpow_natCast δ (4*(2*m+2)),← Real.rpow_add hδ,← Real.rpow_add hδ]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  unfold inputExponent
  push_cast
  field_simp
  ring

theorem output_lower_scaling_real {m : ℕ} (hm : 1 ≤ m) {δ r₀ ε₀ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) :
    thinLowerConstant m*(r₀*δ^3)^m*(ε₀*δ^4)^(2*m+2)*
      (outputDensityScale m δ*M)^(inputExponent m)*
        Real.log ((r₀*δ^3)/(ε₀*δ^4)) =
      outputLowerConstant m r₀ ε₀*δ^((m : ℝ)-2)*M^(inputExponent m)*Real.log (r₀/(ε₀*δ)) := by
  have hlog : (r₀*δ^3)/(ε₀*δ^4)=r₀/(ε₀*δ) := by
    by_cases hε : ε₀=0
    · simp [hε]
    · field_simp
  rw [outputDensityScale_eq m hδ,Real.mul_rpow
    (mul_nonneg (outputDensityConstant_pos m).le (Real.rpow_nonneg hδ.le _)) hM,
    Real.mul_rpow (outputDensityConstant_pos m).le (Real.rpow_nonneg hδ.le _),
    mul_pow,mul_pow,← pow_mul,← pow_mul,hlog]
  have hp := output_delta_power_real hm hδ
  unfold outputLowerConstant
  calc
    _ = (thinLowerConstant m*r₀^m*ε₀^(2*m+2)*(outputDensityConstant m)^(inputExponent m))*
        (δ^(3*m)*δ^(4*(2*m+2))*(δ^(-(10*(m : ℝ))))^(inputExponent m))*
        M^(inputExponent m)*Real.log (r₀/(ε₀*δ)) := by ring
    _ = _ := by rw [hp]

end KakeyaSharp.Packet
