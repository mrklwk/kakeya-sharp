/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.InputSupport

@[expose] public section

/-! Domination of the actual normalized packet density by the input
barrier determinant times a directional weight. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore

def directionWeight {m N : ℕ} (δ : ℝ) (v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (α : Space m) : ℝ :=
  ∑ l, if (∑ j, (α j-v l j)^2) ≤ 5*δ^2 then weights l else 0

theorem directionWeight_nonneg {m N : ℕ} (δ : ℝ) (v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (α : Space m) :
    0 ≤ directionWeight δ v weights α := by
  apply Finset.sum_nonneg
  intro l _
  split_ifs
  · exact hw l
  · rfl

def inputAlpha {m : ℕ} (p : Space 3) (z : ThinSpace m) : Space m :=
  WithLp.toLp 2 (ratioRe (p,z))

def inputDensityConstant (m : ℕ) (A : ℝ) : ℝ :=
  (3*A+12)^(m+1)/((8 : ℝ)^m*cutoffMass m standardCutoff)

theorem inputDensityConstant_pos (m : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 < inputDensityConstant m A := by
  have hZ := standardCutoff_mass_pos m
  unfold inputDensityConstant
  positivity

theorem kakeya_scale_weight (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    δ^m*c/packetMass m (δ^2) (δ^4) standardCutoff =
      c/((δ^4)^m*cutoffMass m standardCutoff) := by
  rw [packetMass_kakeya_scale m hδ]
  have he : δ^(5*m) = δ^m*(δ^4)^m := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he]
  field_simp

theorem kakeyaPacketFamily_density_formula {m N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) (y : ThinCurrentSpace m) :
    currentDensity (kakeyaPacketFamily δ a v weights) y =
      ∑ l, (weights l/((δ^4)^m*cutoffMass m standardCutoff))*
        packetWeight (δ^2) (δ^4) (fun j => δ^2*a l j) (v l) standardCutoff y := by
  simp only [kakeyaPacketFamily, unitPacketFamily, normalizedPacketFamily,
    packetFamily_density, familyWeights, kakeya_scale_weight m hδ]

theorem input_kernel_dominates_constant (m : ℕ) {h A q : ℝ}
    (hh : 0 < h) (hA : 0 ≤ A) (hq : 0 ≤ q) (hqA : q ≤ (3*A+11)*h) :
    1/(h^m*cutoffMass m standardCutoff) ≤
      inputDensityConstant m A*((8 : ℝ)^m*h/(h+q)^(m+1)) := by
  have hZ := standardCutoff_mass_pos m
  have hbase : 0 < h+q := by positivity
  have hC : 0 < 3*A+12 := by positivity
  have hb : h+q ≤ (3*A+12)*h := by nlinarith
  have hp := pow_le_pow_left₀ hbase.le hb (m+1)
  rw [mul_pow] at hp
  unfold inputDensityConstant
  apply (div_le_iff₀ (show 0 < h^m*cutoffMass m standardCutoff by positivity)).mpr
  have he : ((3*A+12)^(m+1)/((8 : ℝ)^m*cutoffMass m standardCutoff)*
      ((8 : ℝ)^m*h/(h+q)^(m+1)))*(h^m*cutoffMass m standardCutoff) =
      (3*A+12)^(m+1)*h^(m+1)/(h+q)^(m+1) := by
    rw [pow_succ h m]
    field_simp
  rw [he]
  exact (one_le_div (pow_pos hbase _)).mpr hp

theorem kakeyaPacketFamily_input_domination {m N : ℕ} (hm : 1 ≤ m)
    {δ A R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (ha : ∀ l, (∑ j, (a l j)^2) ≤ A) {p : Space 3}
    (ht : p 0=0) (hp : (p 1)^2+(p 2)^2=1) (z : ThinSpace m) :
    currentDensity (kakeyaPacketFamily δ a v weights) (p,z) ≤
      (inputDensityConstant m A*directionWeight δ v weights (inputAlpha p z))*
        mooreDet m (thinQuaternionHessian (inputBarrier (δ^4) R (p 1) (p 2)) z) := by
  have hh : 0 < δ^4 := pow_pos hδ 4
  have hZ := standardCutoff_mass_pos m
  have hc := inputDensityConstant_pos m hA
  have hq := inputQuadratic_nonneg (p 1) (p 2) z
  rw [kakeyaPacketFamily_density_formula hδ, inputBarrier_determinant hm hh hp,
    directionWeight, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro l _
  let t := physicalPhase (δ^2) (fun j => δ^2*a l j) (v l) (p,z)/δ^4
  have htau : time (p,z)=(-1) := by simp [time,ht]
  change (weights l/((δ^4)^m*cutoffMass m standardCutoff))*
      (prefactor m (δ^2) (radius (p,z)) (time (p,z))*standardCutoff t) ≤ _
  rw [radius_eq_one_of_unit hp z,htau]
  by_cases hcut : standardCutoff t=0
  · rw [hcut,mul_zero,mul_zero]
    apply mul_nonneg
    · apply mul_nonneg hc.le
      split_ifs
      · exact hw l
      · rfl
    · positivity
  · obtain ⟨hdir,hnormal⟩ := input_cutoff_support hδ hδ1 (a l) (v l) (ha l) ht hp z hcut
    change _ ≤ (inputDensityConstant m A*
      (if (∑ j, (ratioRe (p,z) j-v l j)^2) ≤ 5*δ^2 then weights l else 0))*
        ((8 : ℝ)^m*δ^4/(δ^4+inputQuadratic (p 1) (p 2) z)^(m+1))
    simp only [hdir, ite_true]
    have hpf := prefactor_input_le_one m (pow_pos hδ 2)
    have hcut1 := standardCutoff_le_one t
    have hprod : prefactor m (δ^2) 1 (-1)*standardCutoff t ≤ 1 :=
      (mul_le_mul_of_nonneg_right hpf (standardCutoff_nonneg t)).trans (by simpa using hcut1)
    have h1 := mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ weights l/((δ^4)^m*cutoffMass m standardCutoff) from
        div_nonneg (hw l) (by positivity))
    have h2 := mul_le_mul_of_nonneg_left (input_kernel_dominates_constant m hh hA hq hnormal) (hw l)
    calc
      _ ≤ weights l/((δ^4)^m*cutoffMass m standardCutoff) := by simpa only [mul_one] using h1
      _ ≤ _ := by simpa only [one_div, div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using h2

end KakeyaSharp.Packet
