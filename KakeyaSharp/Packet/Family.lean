/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Conservation
public import KakeyaSharp.Packet.Support

@[expose] public section

/-! Finite weighted sums of the explicit conserved packets, including
their density, flux, stress, and vanishing outside the support bound. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp.Packet
open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Matrix.Norms.Elementwise

def packetFamily {m N : ℕ} (r h : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (χ : ℝ → ℝ) (y : ThinCurrentSpace m) :
    Matrix (Fin (m+1)) (Fin (m+1)) Q := ∑ l, weights l • rawPacket r h (a l) (v l) χ y

def familyWeights {m N : ℕ} (r h : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (χ : ℝ → ℝ) (y : ThinCurrentSpace m) (l : Fin N) : ℝ :=
  weights l*packetWeight r h (a l) (v l) χ y

def familyDirections {m N : ℕ} (r : ℝ) (a v : Fin N → Fin m → ℝ)
    (y : ThinCurrentSpace m) (l : Fin N) (j : Fin m) : Q := physicalColumn r (a l) (v l) y j.succ

theorem packetFamily_contDiffAt {m N : ℕ} {n : ℕ∞ω} {r : ℝ} (hr : 0 < r) (h : ℝ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ n χ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) : ContDiffAt ℝ n (packetFamily r h a v weights χ) y := by
  apply ContDiffAt.sum
  intro l _
  exact (rawPacket_contDiffAt hr h (a l) (v l) hχ hy).const_smul (weights l)

theorem packetFamily_isHermitian {m N : ℕ} (r h : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (χ : ℝ → ℝ) (y : ThinCurrentSpace m) :
    (packetFamily r h a v weights χ y).IsHermitian := by
  unfold packetFamily Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [quaternionMatrix_conjTranspose_real_smul, (rawPacket_isHermitian r h (a l) (v l) χ y).eq]

theorem packetFamily_strongDivergence {m N : ℕ} {r : ℝ} (hr : 0 < r) (h : ℝ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) (j : Fin (m+1)) :
    strongDivergence threeSlots
      (fun p => fderiv ℝ (packetFamily r h a v weights χ) y (currentDirection p)) j = 0 := by
  have hA (l : Fin N) := (rawPacket_contDiffAt hr h (a l) (v l) hχ hy).differentiableAt (by norm_num)
  have he (z : ThinCurrentSpace m) :
      fderiv ℝ (packetFamily r h a v weights χ) y z =
        ∑ l, weights l • fderiv ℝ (rawPacket r h (a l) (v l) χ) y z := by
    have hh := (HasFDerivAt.fun_sum (u := Finset.univ)
      (fun l _ => (hA l).hasFDerivAt.const_smul (weights l))).fderiv
    simpa only [_root_.sum_apply, _root_.smul_apply, packetFamily]
      using! congrArg (fun L => L z) hh
  simp only [strongDivergence, he, Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum, mul_smul_comm]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum]
  change (∑ l, weights l • strongDivergence threeSlots
    (fun p => fderiv ℝ (rawPacket r h (a l) (v l) χ) y (currentDirection p)) j) = 0
  simp only [rawPacket_strongDivergence hr h _ _ hχ hy, smul_zero, Finset.sum_const_zero]

theorem packetFamily_realColumnConservationOn {m N : ℕ} {r : ℝ} (hr : 0 < r) (h : ℝ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    {D : Set (ThinCurrentSpace m)} (hD : ∀ y ∈ D, 0 < radius y) :
    RealColumnConservationOn D (packetFamily r h a v weights χ) := by
  apply realColumnConservationOn_of_strong_at
  · intro y hy
    exact (packetFamily_contDiffAt hr h a v weights hχ (hD y hy)).differentiableAt (by norm_num)
  · intro y hy j
    exact packetFamily_strongDivergence hr h a v weights hχ (hD y hy) j

theorem packetFamily_density {m N : ℕ} (r h : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (χ : ℝ → ℝ) (y : ThinCurrentSpace m) :
    currentDensity (packetFamily r h a v weights χ) y = ∑ l, familyWeights r h a v weights χ y l := by
  simp only [currentDensity, packetFamily, Matrix.sum_apply, Matrix.smul_apply, quaternion_re_sum,
    Quaternion.re_smul, smul_eq_mul, familyWeights]
  apply Finset.sum_congr rfl
  intro l _
  rw [show (rawPacket r h (a l) (v l) χ y 0 0).re = packetWeight r h (a l) (v l) χ y from
    rawPacket_density r h (a l) (v l) χ y]

theorem packetFamily_flux {m N : ℕ} (r h : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (χ : ℝ → ℝ) (y : ThinCurrentSpace m) :
    currentFlux (packetFamily r h a v weights χ) y =
      ∑ l, familyWeights r h a v weights χ y l • familyDirections r a v y l := by
  funext j
  simp [currentFlux, packetFamily, rawPacket, Matrix.sum_apply, Matrix.smul_apply, outer, physicalColumn_zero,
    familyWeights, familyDirections, smul_smul]

theorem packetFamily_stress {m N : ℕ} (r h : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (χ : ℝ → ℝ) (y : ThinCurrentSpace m) :
    currentStress (packetFamily r h a v weights χ) y =
      ∑ l, familyWeights r h a v weights χ y l • outer (familyDirections r a v y l) := by
  funext i j
  simp [currentStress, packetFamily, rawPacket, Matrix.sum_apply, Matrix.smul_apply, outer, familyWeights, familyDirections, smul_smul]

theorem familyWeights_nonneg {m N : ℕ} {r : ℝ} (hr : 0 < r) (h : ℝ)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hweights : ∀ l, 0 ≤ weights l)
    {χ : ℝ → ℝ} (hχ : ∀ u, 0 ≤ χ u) {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (l : Fin N) : 0 ≤ familyWeights r h a v weights χ y l :=
  mul_nonneg (hweights l) (mul_nonneg (prefactor_pos m hr hy _).le (hχ _))

theorem packetFamily_eq_zero_of_supportBound {m N : ℕ} {r h M R : ℝ}
    (hr : 0 < r) (hh : 0 < h) (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    {χ : ℝ → ℝ} (hχ : ∀ u, M < u → χ u=0)
    {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (hbound : ∀ l, supportBound r (h*M) (a l) (v l) y.1 < R^2)
    (hfar : R^2 ≤ ‖y.2.1‖^2+‖y.2.2‖^2) : packetFamily r h a v weights χ y = 0 := by
  apply Finset.sum_eq_zero
  intro l _
  rw [rawPacket_eq_zero_of_supportBound hr hh (a l) (v l) hχ hy (hbound l) hfar, smul_zero]

end KakeyaSharp.Packet
