/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Normalized
public import KakeyaSharp.VariationalParameterContinuity

@[expose] public section

/-! The normalized Kakeya-scale family on a fixed parameter domain. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp.Packet
open MeasureTheory Set KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

def kakeyaPacketFamily {m N : ℕ} (δ : ℝ) (b v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) :=
  unitPacketFamily (δ^2) (δ^4) (fun l j => δ^2*b l j) v (fun l => δ^m*weights l)

theorem kakeyaPacketFamily_mass {m N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (b v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m))) :
    (∫ z : ThinSpace m, currentDensity (kakeyaPacketFamily δ b v weights) (p,z)) =
      δ^m*∑ l, weights l := by
  rw [kakeyaPacketFamily, unitPacketFamily_mass (pow_pos hδ 2) (pow_pos hδ 4) _ _ _ hp,
    Finset.mul_sum]

theorem kakeyaPacketFamily_density_integrable {m N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (b v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m))) :
    Integrable (fun z : ThinSpace m => currentDensity (kakeyaPacketFamily δ b v weights) (p,z)) :=
  normalizedPacketFamily_density_integrable (pow_pos hδ 2) (pow_pos hδ 4) _ _ _ hp
    standardCutoff_smooth.continuous (fun _ ht => standardCutoff_eq_zero ht.le)

def packetDomain (m : ℕ) : Set (Space 3) :=
  {p | (p 0-1)^2 < 16 ∧ 0 < radius (p,(0 : ThinSpace m)) ∧ radius (p,(0 : ThinSpace m)) < 4}

theorem packetDomain_isOpen (m : ℕ) : IsOpen (packetDomain m) := by
  have hs : Continuous (fun p : Space 3 => radius (p,(0 : ThinSpace m))) := by
    unfold radius
    fun_prop
  have ht : Continuous (fun p : Space 3 => (p 0-1)^2) := by fun_prop
  exact (isOpen_lt ht continuous_const).inter
    ((isOpen_lt continuous_const hs).inter (isOpen_lt hs continuous_const))

/-- A spatial radius depending only on the intercept and direction bounds. -/
def packetOuterRadius (A V : ℝ) : ℝ := Real.sqrt (max (4*A+96*V+172) 0)+1

theorem packetOuterRadius_pos (A V : ℝ) : 0 < packetOuterRadius A V := by
  unfold packetOuterRadius
  positivity

theorem packetOuterRadius_sq_gt (A V : ℝ) : 4*A+96*V+172 < packetOuterRadius A V ^ 2 := by
  have h := Real.sq_sqrt (le_max_right (4*A+96*V+172) 0)
  have h' := le_max_left (4*A+96*V+172) 0
  have hs := Real.sqrt_nonneg (max (4*A+96*V+172) 0)
  unfold packetOuterRadius
  nlinarith

theorem supportBound_fixed_radius {m : ℕ} {δ A V : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A)
    (b v : Fin m → ℝ) (hb : (∑ j, (b j)^2) ≤ A) (hv : (∑ j, (v j)^2) ≤ V)
    {p : Space 3} (hp : p ∈ packetDomain m) :
    supportBound (δ^2) (δ^4) (fun j => δ^2*b j) v p < packetOuterRadius A V ^ 2 := by
  have hu := supportBound_uniform hδ hδ1 (show (0 : ℝ) ≤ 1 by norm_num) b v hb hv p hp.1.le hp.2.2.le
  simp only [mul_one] at hu
  have hd2 : δ^2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hd4 : δ^4 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hmul := mul_le_mul_of_nonneg_right hd4 hA
  have hle : 4*δ^4*A+96*V+172*δ^2 ≤ 4*A+96*V+172 := by nlinarith
  exact (hu.trans hle).trans_lt (packetOuterRadius_sq_gt A V)

theorem kakeyaPacketFamily_eq_zero_outside {m N : ℕ} {δ A V : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A)
    (b v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    (hb : ∀ l, (∑ j, (b l j)^2) ≤ A) (hv : ∀ l, (∑ j, (v l j)^2) ≤ V)
    {p : Space 3} (hp : p ∈ packetDomain m) {z : ThinSpace m}
    (hz : packetOuterRadius A V ^ 2 ≤ ‖z.1‖^2+‖z.2‖^2) :
    kakeyaPacketFamily δ b v weights (p,z) = 0 := by
  have hbound : ∀ l, supportBound (δ^2) (δ^4*1) (fun j => δ^2*b l j) (v l) p <
      packetOuterRadius A V ^ 2 := by
    intro l
    simpa only [mul_one] using supportBound_fixed_radius hδ hδ1 hA (b l) (v l) (hb l) (hv l) hp
  unfold kakeyaPacketFamily unitPacketFamily normalizedPacketFamily
  exact packetFamily_eq_zero_of_supportBound (pow_pos hδ 2) (pow_pos hδ 4)
    (fun l j => δ^2*b l j) v _ (R := packetOuterRadius A V) (M := 1)
    (fun _ ht => standardCutoff_eq_zero ht.le) (y := (p,z)) hp.2.1 hbound hz

theorem kakeyaPacketFamily_weakSuperharmonic {m N : ℕ} (hm : 1 ≤ m)
    {δ A V : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A)
    (b v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (hb : ∀ l, (∑ j, (b l j)^2) ≤ A) (hv : ∀ l, (∑ j, (v l j)^2) ≤ V) :
    WeakSuperharmonicOn (packetDomain m) (fun p => thinValueRealAt (packetOuterRadius A V) 0
      (thinSlice (currentDensity (kakeyaPacketFamily δ b v weights)) p)) := by
  apply unitPacketFamily_weakSuperharmonic hm (pow_pos hδ 2) (pow_pos hδ 4)
    (packetOuterRadius_pos A V) _ _ (fun l => mul_nonneg (pow_nonneg hδ.le m) (hw l))
    (packetDomain m) (packetDomain_isOpen m) (fun _ hp => hp.2.1)
  intro p hp l
  exact supportBound_fixed_radius hδ hδ1 hA (b l) (v l) (hb l) (hv l) hp

theorem kakeyaPacketFamily_density_continuous {m N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (b v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    ContinuousOn (currentDensity (kakeyaPacketFamily δ b v weights))
      (packetDomain m ×ˢ (univ : Set (ThinSpace m))) := by
  intro y hy
  have hc : ContDiffAt ℝ 1 (kakeyaPacketFamily δ b v weights) y :=
    packetFamily_contDiffAt (pow_pos hδ 2) (δ^4) (fun l j => δ^2*b l j) v _
      (standardCutoff_smooth.of_le (by simp)) hy.1.2.1
  exact (currentDensity_contDiffAt hc).continuousAt.continuousWithinAt

theorem kakeyaPacketFamily_value_continuous {m N : ℕ} (hm : 1 ≤ m)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (b v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :
    ContinuousOn (fun p => thinValueRealAt R 0
      (thinSlice (currentDensity (kakeyaPacketFamily δ b v weights)) p)) (packetDomain m) :=
  thinValueRealAt_continuousOn_parameter hm hR 0 (packetDomain_isOpen m)
    ((kakeyaPacketFamily_density_continuous hδ b v weights).mono
      (fun _ hy => ⟨hy.1,mem_univ _⟩))

theorem kakeyaPacketFamily_value_nonneg {m N : ℕ} (hm : 1 ≤ m)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (b v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    {p : Space 3} (hp : p ∈ packetDomain m) :
    0 ≤ thinValueRealAt R 0
      (thinSlice (currentDensity (kakeyaPacketFamily δ b v weights)) p) := by
  apply thinValueRealAt_nonneg hm hR 0
  exact (kakeyaPacketFamily_density_continuous hδ b v weights).comp
    (continuous_const.prodMk continuous_id).continuousOn (fun z _ => ⟨hp,mem_univ z⟩)

end KakeyaSharp.Packet
