/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.PhysicalGradient
public import KakeyaSharp.Packet.WeightDerivative
public import KakeyaSharp.Packet.RankOneDerivative

@[expose] public section

/-! The complete strong conservation law for the actual cutoff packet,
in every spatial dimension and at every nonzero parameter Y. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp.Packet
open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Matrix.Norms.Elementwise

def uncutPacket {m : ℕ} (r : ℝ) (a v : Fin m → ℝ) (y : ThinCurrentSpace m) :
    Matrix (Fin (m+1)) (Fin (m+1)) Q := baseWeight r y • outer (physicalColumn r a v y)

theorem uncutPacket_contDiffAt {m : ℕ} {n : ℕ∞ω} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    ContDiffAt ℝ n (uncutPacket r a v) y := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact (baseWeight_contDiffAt hr hy).smul ((physicalColumn_contDiffAt hr a v hy i).mul
    (quaternionStarCLM.contDiff.contDiffAt.comp y (physicalColumn_contDiffAt hr a v hy j)))

theorem uncutPacket_strongDivergence {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y) (j : Fin (m+1)) :
    strongDivergence threeSlots
      (fun p => fderiv ℝ (uncutPacket r a v) y (currentDirection p)) j = 0 := by
  have hf := (baseWeight_contDiffAt (n := 1) hr hy).differentiableAt (by norm_num)
  have hB (i : Fin (m+1)) := (physicalColumn_contDiffAt (n := 1) hr a v hy i).differentiableAt (by norm_num)
  unfold uncutPacket
  rw [strongDivergence_smul_outer threeSlots currentDirection hf hB,
    physicalColumn_weighted_divergence hr a v hy, physicalColumn_acceleration hr a v hy,
    zero_mul, smul_zero, add_zero]

theorem rawPacket_strongDivergence {m : ℕ} {r : ℝ} (hr : 0 < r) (h : ℝ)
    (a v : Fin m → ℝ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) (j : Fin (m+1)) :
    strongDivergence threeSlots
      (fun p => fderiv ℝ (rawPacket r h a v χ) y (currentDirection p)) j = 0 := by
  have hcut : DifferentiableAt ℝ (fun u => χ (u/h)) (physicalPhase r a v y) := by
    exact (hχ.differentiable (by norm_num) _).comp _ (differentiableAt_id.div_const h)
  have hd := strongDivergence_cutoff_rankOne threeSlots currentDirection
    ((uncutPacket_contDiffAt (n := 1) hr a v hy).differentiableAt (by norm_num))
    ((physicalPhase_contDiffAt (n := 1) hr a v hy).differentiableAt (by norm_num))
    hcut (uncutPacket_strongDivergence hr a v hy) (baseWeight r y) (physicalColumn r a v y)
    rfl (physicalColumn_tangency hr a v hy) j
  have he : (fun w => χ (physicalPhase r a v w/h) • uncutPacket r a v w) = rawPacket r h a v χ := by
    funext w
    simp only [uncutPacket, rawPacket, packetWeight, baseWeight, smul_smul, mul_comm]
  rw [he] at hd
  exact hd

theorem rawPacket_realColumnConservationOn {m : ℕ} {r : ℝ} (hr : 0 < r) (h : ℝ)
    (a v : Fin m → ℝ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) :
    RealColumnConservationOn {y : ThinCurrentSpace m | 0 < radius y} (rawPacket r h a v χ) := by
  apply realColumnConservationOn_of_strong_at
  · intro y hy
    exact (rawPacket_contDiffAt hr h a v hχ hy).differentiableAt (by norm_num)
  · intro y hy j
    exact rawPacket_strongDivergence hr h a v hχ hy j

end KakeyaSharp.Packet
