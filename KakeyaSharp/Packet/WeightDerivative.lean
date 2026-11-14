/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.ColumnJet

@[expose] public section

/-! The prefactor balances the divergence of the packet column. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp.Packet
open KakeyaSharp.QuaternionAlgebra
open scoped ContDiff

def baseWeight {m : ℕ} (r : ℝ) (y : ThinCurrentSpace m) : ℝ :=
  prefactor m r (radius y) (time y)

theorem baseWeight_contDiffAt {m : ℕ} {n : ℕ∞ω} {r : ℝ} (hr : 0 < r)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) : ContDiffAt ℝ n (baseWeight r) y := by
  have h := packetWeight_contDiffAt (n := n) hr 1 (fun _ : Fin m => 0) (fun _ => 0)
    (contDiff_const (c := (1 : ℝ))) hy
  have he : packetWeight r 1 (fun _ : Fin m => 0) (fun _ => 0) (fun _ => 1) = baseWeight r := by
    funext w
    simp only [packetWeight, mul_one, baseWeight]
  rw [he] at h
  exact h

theorem baseWeight_fderiv {m : ℕ} {r : ℝ} (hr : 0 < r)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) (z : ThinCurrentSpace m) :
    fderiv ℝ (baseWeight r) y z =
      -(m : ℝ)*(radialRate y z/radius y+
        ((r+radius y)*radialRate y z+time y*z.1 0)/denominator r (radius y) (time y))*baseWeight r y := by
  have he : line y z 0=y := by simp [line]
  apply fderiv_eq_of_line ((baseWeight_contDiffAt (n := 1) hr hy).differentiableAt (by norm_num))
  exact hasDerivAt_prefactor_curve m hr (hasDerivAt_radius_line hy z) (hasDerivAt_time_line y z)
    (congrArg radius he) (congrArg time he) hy

theorem baseWeight_spatial_fderiv {m : ℕ} {r : ℝ} (hr : 0 < r)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) (j : Fin m × Fin 3) :
    fderiv ℝ (baseWeight r) y (spatialDirection j) = 0 := by
  rw [baseWeight_fderiv hr hy]
  simp [radialRate, spatialDirection]

theorem baseWeight_parameter_divergence {m : ℕ} {r : ℝ} (hr : 0 < r)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    (∑ b, fderiv ℝ (baseWeight r) y (parameterDirection b) • star (threeSlots b)) =
      -(m : ℝ) • (baseWeight r y •
        ((time y/denominator r (radius y) (time y) : ℝ)-
          ((r+radius y)/denominator r (radius y) (time y)+1/radius y) •
            orientedI (y.1 1/radius y) (y.1 2/radius y))) := by
  have hs := hy.ne'
  ext <;> simp [Fin.sum_univ_three, baseWeight_fderiv hr hy, parameterDirection,
    radialRate, threeSlots, orientedI, -Quaternion.coe_div] <;> (try field_simp) <;> ring

theorem physicalColumn_weighted_divergence {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    (∑ i : Fin (m+1), ∑ b : Fin 3, (fderiv ℝ (baseWeight r) y (currentDirection (i,b)) •
      (star (threeSlots b)*physicalColumn r a v y i)+
        baseWeight r y • (star (threeSlots b)*
          fderiv ℝ (fun w => physicalColumn r a v w i) y (currentDirection (i,b))))) = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [currentDirection, Fin.cases_zero, Fin.cases_succ,
    physicalColumn_zero, fderiv_const_apply, _root_.zero_apply, mul_one, mul_zero, smul_zero, add_zero,
    baseWeight_spatial_fderiv hr hy, zero_smul, zero_add, ← Finset.smul_sum,
    physicalColumn_spatial_divergence hr a v hy, baseWeight_parameter_divergence hr hy]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  module

end KakeyaSharp.Packet
