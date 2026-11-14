/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Dirichlet
public import KakeyaSharp.Dirichlet.LocalFamily

@[expose] public section

/-! Unconditional scalar transfer for the concrete compact packets.
The Dirichlet families and their boundary representatives are constructed
from the positive regularized sources, then the regularization is removed. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000
namespace KakeyaSharp.Packet
open Set Filter Matrix KakeyaSharp.Dirichlet KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Topology

theorem packetFamily_regularized_value_local_regular
    {m N : ℕ} (hm : 1 ≤ m) {r h R M ε : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hR : 0 < R) (hε : 0 < ε)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχpos : ∀ t, 0 ≤ χ t)
    (hχsupp : ∀ t, M < t → χ t=0)
    (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    (hY : ∀ p ∈ Ω, 0 < radius (p,(0 : ThinSpace m)))
    (hbound : ∀ p ∈ Ω, ∀ l, supportBound r (h*M) (a l) (v l) p < R^2)
    {p : Space 3} (hp : p ∈ Ω) :
    ContDiffAt ℝ 2 (fun q => thinValueRealAt R 0
      (fun z => currentDensity (packetFamily r h a v weights χ) (q,z)+ε)) p ∧
    Laplacian.laplacian (fun q => thinValueRealAt R 0
      (fun z => currentDensity (packetFamily r h a v weights χ) (q,z)+ε)) p ≤ 0 := by
  obtain ⟨U,hs,hl⟩ := packetFamily_regularized_solution_family hm hr hR hε
    h a v hw hχ hχpos Ω hΩ hY
  obtain ⟨W,hW,hpW,hWΩ,V,hV,he,hH⟩ := exists_local_joint_representative hR hΩ
    (fun q hq => (hs q hq).1.of_le (by norm_num))
    (fun q hq z hz => by
      obtain ⟨O,hO,hqz,g,hg,hge⟩ := hl q hq z hz
      exact ⟨O,hO,hqz,g,hg.of_le (by simp),hge⟩) hp
  have hclosed {z : ThinSpace m} (hz : z ∈ thinBallAt R 0) :
      z ∈ thinClosedBallAt R 0 :=
    (show ‖z.1-0‖^2+‖z.2-0‖^2 < R^2 from hz).le
  have hadm : ∀ q ∈ W, ThinAdmissibleAt R 0 (thinSlice V q) := by
    intro q hq
    refine ⟨fun z _ => (thinSlice_contDiff hV q).contDiffAt,?_,?_⟩
    · intro z hz
      exact (he q hq z hz.le).trans ((hs q (hWΩ hq)).2.1.2.1 z hz)
    · intro z hz w
      rw [hH q hq z hz]
      exact (hs q (hWΩ hq)).2.1.2.2 z hz w
  have hy (q : Space 3) (hq : q ∈ W) (z : ThinSpace m) :
      0 < radius (q,z) := hY q (hWΩ hq)
  have hEq : ∀ q ∈ W, ∀ z, z ∈ thinBallAt R 0 →
      mooreDet m (thinQuaternionHessian (thinSlice V q) z) =
        currentDensity (regularizedCurrent (packetFamily r h a v weights χ) ε) (q,z) := by
    intro q hq z hz
    rw [hH q hq z (hclosed hz),currentDensity_regularized]
    exact (hs q (hWΩ hq)).2.2.1 z (hclosed hz)
  have hpositive : ∀ q ∈ W, ∀ z ∈ thinBallAt R 0, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian (thinSlice V q) z) w := by
    intro q hq z hz w hw'
    rw [hH q hq z (hclosed hz)]
    exact (hs q (hWΩ hq)).2.2.2 z (hclosed hz) w hw'
  have hstress : ∀ q ∈ W, ∀ z,
      ‖z.1-0‖^2+‖z.2-0‖^2 = R^2 →
        currentStress (regularizedCurrent (packetFamily r h a v weights χ) ε) (q,z) = 0 := by
    intro q hq z hz
    rw [currentStress_regularized]
    have hz' : R^2 ≤ ‖z.1‖^2+‖z.2‖^2 := by simpa using hz.ge
    have hzero := packetFamily_eq_zero_of_supportBound hr hh a v weights hχsupp
      (hy q hq z) (hbound q (hWΩ hq)) hz'
    funext i j
    change packetFamily r h a v weights χ (q,z) i.succ j.succ = 0
    rw [hzero]
    rfl
  have hlocal := thinValueRealAt_current_local_regular hR 0 W hW
    (fun q _ z _ => hV.contDiffAt) hadm
    (fun q hq z _ => regularizedCurrent_contDiffAt
      (packetFamily_contDiffAt hr h a v weights (hχ.of_le (by simp)) (hy q hq z)) ε)
    (fun y _ => regularizedCurrent_isHermitian_at (packetFamily_isHermitian r h a v weights χ y) ε)
    (regularizedCurrent_conservation_on
      (packetFamily_realColumnConservationOn hr h a v weights (hχ.of_le (by simp))
        (fun y hy' => hy y.1 hy'.1 y.2)) ε)
    hEq hpositive hstress
    (regularizedWeights (familyWeights r h a v weights χ) ε)
    (regularizedDirections (familyDirections r a v))
    (fun q hq z _ => regularizedWeights_nonneg hε.le
      (familyWeights_nonneg hr h a v hw hχpos (hy q hq z)))
    (fun q _ z _ => regularizedCurrent_mass (packetFamily_density r h a v weights χ (q,z)) ε)
    (fun q _ z _ => regularizedCurrent_flux (packetFamily_flux r h a v weights χ (q,z)) ε)
    (fun q _ z _ => regularizedCurrent_stress (packetFamily_stress r h a v weights χ (q,z)) ε)
    p hpW
  have hvalue : (fun q => thinValueRealAt R 0
      (thinSlice (currentDensity (regularizedCurrent (packetFamily r h a v weights χ) ε)) q)) =
      (fun q => thinValueRealAt R 0
        (fun z => currentDensity (packetFamily r h a v weights χ) (q,z)+ε)) := by
    funext q
    congr 1
    funext z
    exact currentDensity_regularized _ ε (q,z)
  rwa [hvalue] at hlocal

/-- Distributional superharmonicity of the actual unregularized packet
variational value, with no PDE solution-family hypothesis. -/
theorem packetFamily_weakSuperharmonic
    {m N : ℕ} (hm : 1 ≤ m) {r h R M : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hR : 0 < R)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχpos : ∀ t, 0 ≤ χ t)
    (hχsupp : ∀ t, M < t → χ t=0)
    (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    (hY : ∀ p ∈ Ω, 0 < radius (p,(0 : ThinSpace m)))
    (hbound : ∀ p ∈ Ω, ∀ l, supportBound r (h*M) (a l) (v l) p < R^2) :
    WeakSuperharmonicOn Ω
      (fun p => thinValueRealAt R 0 (thinSlice (currentDensity (packetFamily r h a v weights χ)) p)) := by
  let ε : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεb (n : ℕ) : ε n ∈ Icc (0 : ℝ) 1 := by
    refine ⟨(hε n).le,?_⟩
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  apply thinValueRealAt_weakSuperharmonic_regularization_on hm hR 0 Ω hΩ
    (fun y hy => (currentDensity_contDiffAt
      (packetFamily_contDiffAt hr h a v weights (hχ.of_le (by simp) : ContDiff ℝ 1 χ)
        (y := y) (hY y.1 hy.1))).continuousAt.continuousWithinAt)
    (show Tendsto ε atTop (nhds 0) from tendsto_one_div_add_atTop_nhds_zero_nat) hεb
  intro n
  have hh' (p : Space 3) (hp : p ∈ Ω) :=
    packetFamily_regularized_value_local_regular hm hr hh hR (hε n)
      a v hw hχ hχpos hχsupp Ω hΩ hY hbound hp
  exact weakSuperharmonicOn_of_contDiffOn_laplacian_nonpos hΩ
    (fun p hp => (hh' p hp).1.contDiffWithinAt) (fun p hp => (hh' p hp).2)

end KakeyaSharp.Packet
