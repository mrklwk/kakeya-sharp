/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.KakeyaFamily
public import KakeyaSharp.Propagation.SingleLog
public import KakeyaSharp.Propagation.WeakSingleLog

@[expose] public section

/-! A fixed packet domain containing the full propagation cylinder, with
an explicit spatial support radius independent of the Kakeya scale. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open MeasureTheory Set KakeyaSharp.Green OAI.Analysis.PDE.Concentration
open scoped ContDiff Matrix.Norms.Elementwise

def propagationPacketDomain (m : ℕ) : Set (Space 3) :=
  {p | (p 0-1)^2 < 576 ∧ 0 < radius (p,(0 : ThinSpace m)) ∧ radius (p,(0 : ThinSpace m)) < 5}

theorem propagationPacketDomain_isOpen (m : ℕ) : IsOpen (propagationPacketDomain m) := by
  have hs : Continuous (fun p : Space 3 => radius (p,(0 : ThinSpace m))) := by unfold radius; fun_prop
  have ht : Continuous (fun p : Space 3 => (p 0-1)^2) := by fun_prop
  exact (isOpen_lt ht continuous_const).inter
    ((isOpen_lt continuous_const hs).inter (isOpen_lt hs continuous_const))

def propagationOuterRadius (A V : ℝ) : ℝ := Real.sqrt (max (4*A+2354*V+2458) 0)+1

theorem propagationOuterRadius_pos (A V : ℝ) : 0 < propagationOuterRadius A V := by
  unfold propagationOuterRadius
  positivity

theorem propagationOuterRadius_sq_gt (A V : ℝ) :
    4*A+2354*V+2458 < propagationOuterRadius A V^2 := by
  have h := Real.sq_sqrt (le_max_right (4*A+2354*V+2458) 0)
  have h' := le_max_left (4*A+2354*V+2458) 0
  have hs := Real.sqrt_nonneg (max (4*A+2354*V+2458) 0)
  unfold propagationOuterRadius
  nlinarith

theorem supportBound_propagation_uniform {m : ℕ} {δ A V : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (a v : Fin m → ℝ)
    (ha : (∑ j, (a j)^2) ≤ A) (hv : (∑ j, (v j)^2) ≤ V)
    {p : Space 3} (hp : p ∈ propagationPacketDomain m) :
    supportBound (δ^2) (δ^4) (fun j => δ^2*a j) v p < propagationOuterRadius A V^2 := by
  let s := radius (p,(0 : ThinSpace m))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs5 : s ≤ 5 := hp.2.2.le
  have hs2 : s^2 ≤ 25 := by nlinarith
  have ht : (p 0-1)^2 ≤ 576 := hp.1.le
  have hd2 : δ^2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hd4 : δ^4 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hA : 0 ≤ A := (Finset.sum_nonneg (fun j _ => sq_nonneg (a j))).trans ha
  have hV : 0 ≤ V := (Finset.sum_nonneg (fun j _ => sq_nonneg (v j))).trans hv
  have he : supportBound (δ^2) (δ^4) (fun j => δ^2*a j) v p =
      4*δ^4*(∑ j, (a j)^2)+(4*(p 0-1)^2+2*s^2)*(∑ j, (v j)^2)+
        δ^2*(4*(p 0-1)^2+4*δ^4+10*δ^2*s+4*s^2) := by
    unfold supportBound
    simp only [mul_pow,← Finset.mul_sum]
    dsimp only [s]
    have hd := hδ.ne'
    field_simp
    ring
  have hds : δ^2*s ≤ 5 := (mul_le_mul_of_nonneg_right hd2 hs0).trans (by simpa using hs5)
  have hcoef : 4*(p 0-1)^2+4*δ^4+10*δ^2*s+4*s^2 ≤ 2458 := by nlinarith
  have hcoefv : 4*(p 0-1)^2+2*s^2 ≤ 2354 := by nlinarith
  rw [he]
  calc
    _ ≤ 4*δ^4*A+2354*V+δ^2*2458 := by gcongr
    _ ≤ 4*A+2354*V+2458 := by nlinarith [mul_le_mul_of_nonneg_right hd4 hA]
    _ < _ := propagationOuterRadius_sq_gt A V

theorem kakeyaPacketFamily_propagation_weakSuperharmonic {m N : ℕ} (hm : 1 ≤ m)
    {δ A V : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (ha : ∀ l, (∑ j, (a l j)^2) ≤ A) (hv : ∀ l, (∑ j, (v l j)^2) ≤ V) :
    WeakSuperharmonicOn (propagationPacketDomain m) (fun p =>
      thinValueRealAt (propagationOuterRadius A V) 0
        (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) p)) := by
  apply unitPacketFamily_weakSuperharmonic hm (pow_pos hδ 2) (pow_pos hδ 4)
    (propagationOuterRadius_pos A V) _ _ (fun l => mul_nonneg (pow_nonneg hδ.le m) (hw l))
    (propagationPacketDomain m) (propagationPacketDomain_isOpen m) (fun _ hp => hp.2.1)
  intro p hp l
  exact supportBound_propagation_uniform hδ hδ1 (a l) (v l) (ha l) (hv l) hp

theorem kakeyaPacketFamily_propagation_density_continuous {m N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    ContinuousOn (currentDensity (kakeyaPacketFamily δ a v weights))
      (propagationPacketDomain m ×ˢ (univ : Set (ThinSpace m))) := by
  intro y hy
  have hc : ContDiffAt ℝ 1 (kakeyaPacketFamily δ a v weights) y :=
    packetFamily_contDiffAt (pow_pos hδ 2) (δ^4) (fun l j => δ^2*a l j) v _
      (standardCutoff_smooth.of_le (by simp)) hy.1.2.1
  exact (currentDensity_contDiffAt hc).continuousAt.continuousWithinAt

theorem kakeyaPacketFamily_propagation_value_continuous {m N : ℕ} (hm : 1 ≤ m)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    ContinuousOn (fun p => thinValueRealAt R 0
      (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) p)) (propagationPacketDomain m) :=
  thinValueRealAt_continuousOn_parameter hm hR 0 (propagationPacketDomain_isOpen m)
    ((kakeyaPacketFamily_propagation_density_continuous hδ a v weights).mono
      (fun _ hy => ⟨hy.1,mem_univ _⟩))

theorem kakeyaPacketFamily_propagation_value_nonneg {m N : ℕ} (hm : 1 ≤ m)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    {p : Space 3} (hp : p ∈ propagationPacketDomain m) :
    0 ≤ thinValueRealAt R 0
      (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) p) := by
  apply thinValueRealAt_nonneg hm hR 0
  exact (kakeyaPacketFamily_propagation_density_continuous hδ a v weights).comp
    (continuous_const.prodMk continuous_id).continuousOn (fun z _ => ⟨hp,mem_univ z⟩)

theorem cylinderCompact_subset_propagationPacketDomain (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Propagation.cylinderCompact ρ ⊆ propagationPacketDomain m := by
  intro p hp
  have ht : p 0 ∈ Icc (-cylinderTimeEnd-1) (cylinderTimeEnd+1) := hp.1
  have hr : radius (p,(0 : ThinSpace m))=‖(cylinderComplexEquiv p).2‖ := by
    rw [radius,Complex.norm_def,cylinderComplexEquiv_apply]
    simp [Complex.normSq_apply,pow_two]
  have htbound : (p 0-1)^2 < 576 := by
    dsimp [cylinderTimeEnd] at ht
    have hl : -24 < p 0-1 := by linarith [Real.pi_lt_four,ht.1]
    have hu : p 0-1 < 24 := by linarith [Real.pi_lt_four,ht.2]
    nlinarith
  exact ⟨htbound,by rw [hr]; linarith [hp.2.1],by rw [hr]; linarith [hp.2.2]⟩

end KakeyaSharp.Packet
