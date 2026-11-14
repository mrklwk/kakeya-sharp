/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Phase

@[expose] public section

/-! Positivity and actual derivatives of the packet density prefactor. -/
noncomputable section
namespace KakeyaSharp.Packet

def prefactor (m : ℕ) (r s τ : ℝ) : ℝ :=
  (s^2*denominator r s τ)^(-(m : ℝ)/2)

theorem prefactor_pos (m : ℕ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (τ : ℝ) :
    0 < prefactor m r s τ :=
  Real.rpow_pos_of_pos (mul_pos (sq_pos_of_pos hs) (denominator_pos hr hs τ)) _

theorem hasDerivAt_prefactor_curve (m : ℕ) {r : ℝ} (hr : 0 < r)
    {S T : ℝ → ℝ} {s τ s' τ' t : ℝ}
    (hS : HasDerivAt S s' t) (hT : HasDerivAt T τ' t)
    (hSv : S t=s) (hTv : T t=τ) (hs : 0 < s) :
    HasDerivAt (fun u => prefactor m r (S u) (T u))
      (-(m : ℝ)*(s'/s+((r+s)*s'+τ*τ')/denominator r s τ)*prefactor m r s τ) t := by
  have hD := ((hS.const_add r).pow 2).add (hT.pow 2)
  have hbase := (hS.pow 2).mul hD
  have hden : (r+s)^2+τ^2 ≠ 0 := (denominator_pos hr hs τ).ne'
  have hb : s^2*((r+s)^2+τ^2) ≠ 0 := mul_ne_zero (pow_ne_zero _ hs.ne') hden
  have hne : (S t)^2*((r+S t)^2+(T t)^2) ≠ 0 := by simpa only [hSv,hTv] using hb
  refine (hbase.rpow_const (Or.inl hne)).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, hSv,hTv,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [Real.rpow_sub_one hb]
  unfold prefactor denominator
  field_simp

theorem prefactor_tau (m : ℕ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (τ : ℝ) :
    deriv (prefactor m r s) τ = -(m : ℝ)*τ/denominator r s τ*prefactor m r s τ := by
  have h := (hasDerivAt_prefactor_curve m hr (hasDerivAt_const τ s) (hasDerivAt_id τ)
    rfl rfl hs).deriv
  simpa only [id_eq, zero_div, zero_mul, mul_zero, add_zero, zero_add, mul_one, mul_div_assoc] using h

theorem prefactor_s (m : ℕ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (τ : ℝ) :
    deriv (fun y => prefactor m r y τ) s =
      -(m : ℝ)*(1/s+(r+s)/denominator r s τ)*prefactor m r s τ := by
  simpa only [id_eq, mul_zero, add_zero, mul_one] using
    (hasDerivAt_prefactor_curve m hr (hasDerivAt_id s) (hasDerivAt_const s τ) rfl rfl hs).deriv

end KakeyaSharp.Packet
