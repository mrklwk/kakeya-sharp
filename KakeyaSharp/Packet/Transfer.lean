/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Family
public import KakeyaSharp.ThinCurrentWeakOn

@[expose] public section

/-! Scalar transfer for the concrete weighted packet family. Conservation,
Hermitian symmetry, positive block decomposition, and boundary vanishing
are proved from the formulas. The regularized Dirichlet families remain
an explicit analytic assumption, including their parameter regularity. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp.Packet
open Matrix Set Filter KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem packetFamily_weakSuperharmonic_of_regularized_solutions
    {m N : ℕ} (hm : 1 ≤ m) {r h R M : ℝ} (hr : 0 < r) (hh : 0 < h) (hR : 0 < R)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hweights : ∀ l, 0 ≤ weights l)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχpos : ∀ u, 0 ≤ χ u)
    (hχsupp : ∀ u, M < u → χ u=0)
    (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    (hY : ∀ p ∈ Ω, 0 < radius (p, (0 : ThinSpace m)))
    (hbound : ∀ p ∈ Ω, ∀ l, supportBound r (h*M) (a l) (v l) p < R^2)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hεb : ∀ n, ε n ∈ Ioc (0 : ℝ) 1)
    (U : ℕ → ThinCurrentSpace m → ℝ)
    (hU : ∀ n p, p ∈ Ω → ∀ z ∈ thinClosedBallAt R 0, ContDiffAt ℝ 3 (U n) (p,z))
    (hadm : ∀ n p, p ∈ Ω → ThinAdmissibleAt R 0 (thinSlice (U n) p))
    (hEq : ∀ n p, p ∈ Ω → ∀ z, z ∈ thinBallAt R 0 →
      mooreDet m (thinQuaternionHessian (thinSlice (U n) p) z) =
        currentDensity (packetFamily r h a v weights χ) (p,z)+ε n)
    (hpos : ∀ n p, p ∈ Ω → ∀ z ∈ thinBallAt R 0, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian (thinSlice (U n) p) z) w) :
    WeakSuperharmonicOn Ω
      (fun p => thinValueRealAt R 0 (thinSlice (currentDensity (packetFamily r h a v weights χ)) p)) := by
  have hy (p : Space 3) (hp : p ∈ Ω) (z : ThinSpace m) : 0 < radius (p,z) := hY p hp
  apply thinValueRealAt_current_weakSuperharmonic_of_local_regularized_solutions hm hR 0 Ω hΩ
    (fun p hp z _ => packetFamily_contDiffAt hr h a v weights hχ (hy p hp z))
    (fun y _ => packetFamily_isHermitian r h a v weights χ y)
    (packetFamily_realColumnConservationOn hr h a v weights (hχ.of_le (by norm_num))
      (fun y hy' => hy y.1 hy'.1 y.2)) hε hεb U hU hadm hEq hpos
    ?_ (familyWeights r h a v weights χ) (familyDirections r a v)
    (fun p hp z _ l => familyWeights_nonneg hr h a v hweights hχpos (hy p hp z) l)
    (fun p _ z _ => packetFamily_density r h a v weights χ (p,z))
    (fun p _ z _ => packetFamily_flux r h a v weights χ (p,z))
    (fun p _ z _ => packetFamily_stress r h a v weights χ (p,z))
  intro p hp z hz
  have hz' : R^2 ≤ ‖z.1‖^2+‖z.2‖^2 := by simpa using hz.ge
  have he := packetFamily_eq_zero_of_supportBound hr hh a v weights hχsupp (hy p hp z) (hbound p hp) hz'
  funext i j
  change packetFamily r h a v weights χ (p,z) i.succ j.succ = 0
  rw [he]
  rfl

end KakeyaSharp.Packet
