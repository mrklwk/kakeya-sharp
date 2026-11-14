/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Physical
public import KakeyaSharp.Packet.PhaseDerivative

@[expose] public section

/-! The explicit packet is smooth wherever the parameter Y is nonzero.
This supplies the local regularity required by the scalar-transfer theorem. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp.Packet
open KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Matrix.Norms.Elementwise

theorem radius_contDiffAt {m : ℕ} {n : ℕ∞ω} {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    ContDiffAt ℝ n (@radius m) y := by
  have hq : (y.1 1)^2+(y.1 2)^2 ≠ 0 := (Real.sqrt_pos.mp hy).ne'
  have hsq : ContDiffAt ℝ n (fun z : ThinCurrentSpace m => (z.1 1)^2+(z.1 2)^2) y := by fun_prop
  exact hsq.sqrt hq

theorem ratioRe_contDiffAt {m : ℕ} {n : ℕ∞ω} {y : ThinCurrentSpace m}
    (hy : 0 < radius y) (j : Fin m) : ContDiffAt ℝ n (fun z => ratioRe z j) y := by
  have hq : (y.1 1)^2+(y.1 2)^2 ≠ 0 := (Real.sqrt_pos.mp hy).ne'
  unfold ratioRe
  fun_prop (disch := exact hq)

theorem ratioIm_contDiffAt {m : ℕ} {n : ℕ∞ω} {y : ThinCurrentSpace m}
    (hy : 0 < radius y) (j : Fin m) : ContDiffAt ℝ n (fun z => ratioIm z j) y := by
  have hq : (y.1 1)^2+(y.1 2)^2 ≠ 0 := (Real.sqrt_pos.mp hy).ne'
  unfold ratioIm
  fun_prop (disch := exact hq)

theorem centers_contDiffAt {m : ℕ} {n : ℕ∞ω} {r : ℝ} (hr : 0 < r) (a v : Fin m → ℝ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) (j : Fin m) :
    ContDiffAt ℝ n (fun z => centers r a v z j) y := by
  have hS : ContDiffAt ℝ n (@radius m) y := radius_contDiffAt hy
  have hα : ContDiffAt ℝ n (fun z => ratioRe z j) y := ratioRe_contDiffAt hy j
  have hD : (r+radius y)^2+(time y)^2 ≠ 0 := (denominator_pos hr hy _).ne'
  unfold centers center denominator time at *
  fun_prop (disch := exact hD)

theorem residuals_contDiffAt {m : ℕ} {n : ℕ∞ω} {r : ℝ} (hr : 0 < r) (a v : Fin m → ℝ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) (j : Fin m) :
    ContDiffAt ℝ n (fun z => residuals r a v z j) y := by
  have hS : ContDiffAt ℝ n (@radius m) y := radius_contDiffAt hy
  have hα : ContDiffAt ℝ n (fun z => ratioRe z j) y := ratioRe_contDiffAt hy j
  have hD : (r+radius y)^2+(time y)^2 ≠ 0 := (denominator_pos hr hy _).ne'
  unfold residuals residual denominator time at *
  fun_prop (disch := exact hD)

theorem physicalPhase_contDiffAt {m : ℕ} {n : ℕ∞ω} {r : ℝ} (hr : 0 < r) (a v : Fin m → ℝ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) : ContDiffAt ℝ n (physicalPhase r a v) y := by
  have hS : ContDiffAt ℝ n (@radius m) y := radius_contDiffAt hy
  have hK : r+radius y ≠ 0 := (add_pos hr hy).ne'
  unfold physicalPhase phase scalarPhase scalarEnergy
  apply ContDiffAt.sum
  intro j _
  have hα : ContDiffAt ℝ n (fun z => ratioRe z j) y := ratioRe_contDiffAt hy j
  have hβ : ContDiffAt ℝ n (fun z => ratioIm z j) y := ratioIm_contDiffAt hy j
  have hc := centers_contDiffAt (n := n) hr a v hy j
  unfold centers at hc
  unfold time at *
  fun_prop (disch := exact hK)

theorem columnEntry_linear (u v α β c d : ℝ) :
    columnEntry u v α β c d = ((α+c)/2) • (1 : Q)+(-u*d/2) • threeSlots 1+
      (-v*d/2) • threeSlots 2+(β/2) • unitK := by
  ext <;> simp [columnEntry, threeSlots, unitK]

theorem physicalColumn_contDiffAt {m : ℕ} {n : ℕ∞ω} {r : ℝ} (hr : 0 < r) (a v : Fin m → ℝ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) (j : Fin (m+1)) :
    ContDiffAt ℝ n (fun z => physicalColumn r a v z j) y := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [physicalColumn_zero] using (contDiffAt_const : ContDiffAt ℝ n (fun _ : ThinCurrentSpace m => (1 : Q)) y)
  · have hS : ContDiffAt ℝ n (@radius m) y := radius_contDiffAt hy
    have hα : ContDiffAt ℝ n (fun z => ratioRe z j) y := ratioRe_contDiffAt hy j
    have hβ : ContDiffAt ℝ n (fun z => ratioIm z j) y := ratioIm_contDiffAt hy j
    have hc := centers_contDiffAt (n := n) hr a v hy j
    have hd := residuals_contDiffAt (n := n) hr a v hy j
    simp only [physicalColumn, column, Fin.cases_succ, columnEntry_linear]
    fun_prop (disch := exact hy.ne')

theorem packetWeight_contDiffAt {m : ℕ} {n : ℕ∞ω} {r : ℝ} (hr : 0 < r) (h : ℝ)
    (a v : Fin m → ℝ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ n χ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) : ContDiffAt ℝ n (packetWeight r h a v χ) y := by
  have hS : ContDiffAt ℝ n (@radius m) y := radius_contDiffAt hy
  have hφ := physicalPhase_contDiffAt (n := n) hr a v hy
  have hbase : (radius y)^2*((r+radius y)^2+(time y)^2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hy.ne') (denominator_pos hr hy _).ne'
  unfold packetWeight prefactor denominator time at *
  fun_prop (disch := exact hbase)

theorem rawPacket_contDiffAt {m : ℕ} {n : ℕ∞ω} {r : ℝ} (hr : 0 < r) (h : ℝ)
    (a v : Fin m → ℝ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ n χ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) : ContDiffAt ℝ n (rawPacket r h a v χ) y := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact (packetWeight_contDiffAt hr h a v hχ hy).smul
    ((physicalColumn_contDiffAt hr a v hy i).mul
      (quaternionStarCLM.contDiff.contDiffAt.comp y (physicalColumn_contDiffAt hr a v hy j)))

end KakeyaSharp.Packet
