/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Phase

@[expose] public section

/-! Actual derivatives of the packet minimizer. The transport identities
are consequences of the rational formulas, not hypotheses. -/
noncomputable section
namespace KakeyaSharp.Packet

theorem hasDerivAt_center_curve {r a v : ℝ} (hr : 0 < r)
    {S T X A : ℝ → ℝ} {s τ x α s' τ' x' α' t : ℝ}
    (hS : HasDerivAt S s' t) (hT : HasDerivAt T τ' t)
    (hX : HasDerivAt X x' t) (hA : HasDerivAt A α' t)
    (hSv : S t=s) (hTv : T t=τ) (hXv : X t=x) (hAv : A t=α) (hs : 0 < s) :
    HasDerivAt (fun u => center r (S u) (T u) a v (X u) (A u))
      (((r+s)*(s'*(α-center r s τ a v x α)+s*α'+τ'*residual r s τ a v x α)+
        τ*(x'-τ'*center r s τ a v x α-s'*residual r s τ a v x α))/denominator r s τ) t := by
  have hK := hS.const_add r
  have hU := (hS.mul hA).const_add (r*v)
  have hV := hX.sub_const a
  have hN := (hK.mul hU).add (hT.mul hV)
  have hD := (hK.pow 2).add (hT.pow 2)
  have hne : (r+S t)^2+(T t)^2 ≠ 0 := by
    rw [hSv,hTv]
    exact (denominator_pos hr hs τ).ne'
  have hden : (r+s)^2+τ^2 ≠ 0 := (denominator_pos hr hs τ).ne'
  refine (hN.div hD hne).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, hSv,hTv,hXv,hAv,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  unfold center residual denominator
  field_simp
  ring

theorem hasDerivAt_residual_curve {r a v : ℝ} (hr : 0 < r)
    {S T X A : ℝ → ℝ} {s τ x α s' τ' x' α' t : ℝ}
    (hS : HasDerivAt S s' t) (hT : HasDerivAt T τ' t)
    (hX : HasDerivAt X x' t) (hA : HasDerivAt A α' t)
    (hSv : S t=s) (hTv : T t=τ) (hXv : X t=x) (hAv : A t=α) (hs : 0 < s) :
    HasDerivAt (fun u => residual r (S u) (T u) a v (X u) (A u))
      (((r+s)*(x'-τ'*center r s τ a v x α-s'*residual r s τ a v x α)-
        τ*(s'*(α-center r s τ a v x α)+s*α'+τ'*residual r s τ a v x α))/denominator r s τ) t := by
  have hK := hS.const_add r
  have hU := (hS.mul hA).const_add (r*v)
  have hV := hX.sub_const a
  have hN := (hK.mul hV).sub (hT.mul hU)
  have hD := (hK.pow 2).add (hT.pow 2)
  have hne : (r+S t)^2+(T t)^2 ≠ 0 := by
    rw [hSv,hTv]
    exact (denominator_pos hr hs τ).ne'
  have hden : (r+s)^2+τ^2 ≠ 0 := (denominator_pos hr hs τ).ne'
  refine (hN.div hD hne).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, hSv,hTv,hXv,hAv,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  unfold center residual denominator
  field_simp
  ring

theorem center_x {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (τ a v x α : ℝ) :
    deriv (fun y => center r s τ a v y α) x = τ/denominator r s τ := by
  simpa using (hasDerivAt_center_curve (a := a) (v := v) hr (hasDerivAt_const x s) (hasDerivAt_const x τ)
    (hasDerivAt_id x) (hasDerivAt_const x α) rfl rfl rfl rfl hs).deriv

theorem residual_x {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (τ a v x α : ℝ) :
    deriv (fun y => residual r s τ a v y α) x = (r+s)/denominator r s τ := by
  simpa using (hasDerivAt_residual_curve (a := a) (v := v) hr (hasDerivAt_const x s) (hasDerivAt_const x τ)
    (hasDerivAt_id x) (hasDerivAt_const x α) rfl rfl rfl rfl hs).deriv

theorem center_alpha {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (τ a v x α : ℝ) :
    deriv (fun y => center r s τ a v x y) α =
      s*deriv (fun y => residual r s τ a v y α) x := by
  have h := (hasDerivAt_center_curve (a := a) (v := v) hr (hasDerivAt_const α s) (hasDerivAt_const α τ)
    (hasDerivAt_const α x) (hasDerivAt_id α) rfl rfl rfl rfl hs).deriv
  rw [residual_x hr hs]
  simp only [id_eq] at h
  rw [h]
  ring

theorem residual_alpha {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (τ a v x α : ℝ) :
    deriv (fun y => residual r s τ a v x y) α =
      -s*deriv (fun y => center r s τ a v y α) x := by
  have h := (hasDerivAt_residual_curve (a := a) (v := v) hr (hasDerivAt_const α s) (hasDerivAt_const α τ)
    (hasDerivAt_const α x) (hasDerivAt_id α) rfl rfl rfl rfl hs).deriv
  rw [center_x hr hs]
  simp only [id_eq] at h
  rw [h]
  ring

theorem center_transport {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (τ a v x α : ℝ) :
    deriv (fun t => center r s t a v x α) τ +
      deriv (fun t => residual r t τ a v x α) s +
        α*deriv (fun t => center r s τ a v t α) x = 0 := by
  have ht := (hasDerivAt_center_curve (a := a) (v := v) hr (hasDerivAt_const τ s) (hasDerivAt_id τ)
    (hasDerivAt_const τ x) (hasDerivAt_const τ α) rfl rfl rfl rfl hs).deriv
  have hs' := (hasDerivAt_residual_curve (a := a) (v := v) hr (hasDerivAt_id s) (hasDerivAt_const s τ)
    (hasDerivAt_const s x) (hasDerivAt_const s α) rfl rfl rfl rfl hs).deriv
  simp only [id_eq] at ht hs'
  rw [ht, hs', center_x hr hs]
  ring

theorem residual_transport {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (τ a v x α : ℝ) :
    deriv (fun t => residual r s t a v x α) τ -
      deriv (fun t => center r t τ a v x α) s +
        α*deriv (fun t => residual r s τ a v t α) x = 0 := by
  have ht := (hasDerivAt_residual_curve (a := a) (v := v) hr (hasDerivAt_const τ s) (hasDerivAt_id τ)
    (hasDerivAt_const τ x) (hasDerivAt_const τ α) rfl rfl rfl rfl hs).deriv
  have hs' := (hasDerivAt_center_curve (a := a) (v := v) hr (hasDerivAt_id s) (hasDerivAt_const s τ)
    (hasDerivAt_const s x) (hasDerivAt_const s α) rfl rfl rfl rfl hs).deriv
  simp only [id_eq] at ht hs'
  rw [ht, hs', residual_x hr hs]
  ring

end KakeyaSharp.Packet
