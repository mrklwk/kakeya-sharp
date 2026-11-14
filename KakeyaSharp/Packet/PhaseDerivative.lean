/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Transport

@[expose] public section

/-! Differentiation of the actual minimized phase along arbitrary smooth
curves. The derivative of the minimizing center cancels by its equations. -/
noncomputable section
namespace KakeyaSharp.Packet

theorem hasDerivAt_energy_at_center {r a v : ℝ} (hr : 0 < r)
    {S T X A B C : ℝ → ℝ} {s τ x α β c d s' τ' x' α' β' c' t : ℝ}
    (hS : HasDerivAt S s' t) (hT : HasDerivAt T τ' t)
    (hX : HasDerivAt X x' t) (hA : HasDerivAt A α' t)
    (hB : HasDerivAt B β' t) (hC : HasDerivAt C c' t)
    (hSv : S t=s) (hTv : T t=τ) (hXv : X t=x) (hAv : A t=α)
    (hBv : B t=β) (hCv : C t=c) (hs : 0 < s)
    (hc : (r+s)*c-τ*d=r*v+s*α) (hd : τ*c+(r+s)*d=x-a) :
    HasDerivAt (fun u => scalarEnergy r (S u) (T u) a v (X u) (A u) (B u) (C u))
      (2*d*x'-2*c*d*τ'+s'*((α-c)^2+β^2-d^2)+2*s*(α-c)*α'+2*s*β*β') t := by
  have hK := hS.const_add r
  have hV := (hX.sub_const a).sub (hT.mul hC)
  have hne : r+S t ≠ 0 := by rw [hSv]; exact (add_pos hr hs).ne'
  have h := (((((hC.sub_const v).pow 2).const_mul r).add
    ((hV.pow 2).div hK hne)).add (hS.mul ((hA.sub hC).pow 2))).add (hS.mul (hB.pow 2))
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, hSv,hTv,hXv,hAv,hBv,hCv,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [show x-a-τ*c=(r+s)*d by linarith]
  have hKne := (add_pos hr hs).ne'
  field_simp
  linear_combination 2*c'*hc

theorem hasDerivAt_scalarPhase_curve {r a v : ℝ} (hr : 0 < r)
    {S T X A B : ℝ → ℝ} {s τ x α β s' τ' x' α' β' t : ℝ}
    (hS : HasDerivAt S s' t) (hT : HasDerivAt T τ' t)
    (hX : HasDerivAt X x' t) (hA : HasDerivAt A α' t) (hB : HasDerivAt B β' t)
    (hSv : S t=s) (hTv : T t=τ) (hXv : X t=x) (hAv : A t=α) (hBv : B t=β) (hs : 0 < s) :
    HasDerivAt (fun u => scalarPhase r (S u) (T u) a v (X u) (A u) (B u))
      (2*residual r s τ a v x α*x'-2*center r s τ a v x α*residual r s τ a v x α*τ'+
        s'*((α-center r s τ a v x α)^2+β^2-(residual r s τ a v x α)^2)+
        2*s*(α-center r s τ a v x α)*α'+2*s*β*β') t := by
  have hC := hasDerivAt_center_curve (a := a) (v := v) hr hS hT hX hA hSv hTv hXv hAv hs
  have hCv : center r (S t) (T t) a v (X t) (A t) = center r s τ a v x α := by
    rw [hSv,hTv,hXv,hAv]
  obtain ⟨hc,hd⟩ := center_equations hr hs τ a v x α
  exact hasDerivAt_energy_at_center hr hS hT hX hA hB hC hSv hTv hXv hAv hBv hCv hs hc hd

end KakeyaSharp.Packet
