/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.OutputDensity
public import KakeyaSharp.VariationalLocalization

@[expose] public section

/-! Logarithmic output lower bounds for the actual packet family on a
finite collection of disjoint balls. The source lower bound is derived from
explicit packet-axis geometry and the fixed cutoff. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory
open scoped ContDiff

def outputAxis {m : ℕ} (δ : ℝ) (a v : Fin m → ℝ) (p : Space 3) : Space m :=
  WithLp.toLp 2 (fun j => δ^2*a j+(p 0-1)*v j)

theorem output_core_error {m : ℕ} {δ R ε : ℝ} (_hδ : 0 < δ)
    (a v : Fin m → ℝ) (p : Space 3) (c : ThinSpace m)
    (hR : R ≤ δ^3/4) (hc : ‖c.1-outputAxis δ a v p‖ ≤ δ^3/8)
    {z : ThinSpace m} (hz : z ∈ thinCoreAt R ε c) :
    (∑ j, (z.1 j-δ^2*a j-time (p,z)*v j)^2) ≤ δ^2*δ^4/16 := by
  have hx : ‖z.1-c.1‖ < R/2 := by simpa only [mem_ball,dist_eq_norm] using hz.1
  have ht := norm_sub_le_norm_sub_add_norm_sub z.1 c.1 (outputAxis δ a v p)
  have hd : ‖z.1-outputAxis δ a v p‖ ≤ δ^3/4 := by linarith
  have hs : ‖z.1-outputAxis δ a v p‖^2 ≤ δ^2*δ^4/16 := by
    nlinarith [norm_nonneg (z.1-outputAxis δ a v p)]
  simpa [EuclideanSpace.real_norm_sq_eq,outputAxis,time,sub_add_eq_sub_sub] using hs

theorem kakeyaPacketFamily_density_slice_smooth {m N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) {p : Space 3}
    (hp : 0 < radius (p,(0 : ThinSpace m))) :
    ContDiff ℝ ∞ (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) p) := by
  exact packetFamily_density_slice_smooth (pow_pos hδ 2) (δ^4)
    (fun l j => δ^2*a l j) v _ standardCutoff_smooth hp

theorem kakeyaPacketFamily_density_nonneg {m N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    0 ≤ currentDensity (kakeyaPacketFamily δ a v weights) y := by
  rw [kakeyaPacketFamily_density_formula hδ a v weights]
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (div_nonneg (hw l)
    (mul_pos (pow_pos (pow_pos hδ 4) m) (standardCutoff_mass_pos m)).le)
    (mul_nonneg (prefactor_pos m (pow_pos hδ 2) hy _).le (standardCutoff_nonneg _))

theorem kakeyaPacketFamily_localized_output_lower {m N J : ℕ} (hm : 1 ≤ m)
    {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 < R)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (r ε : Fin J → ℝ) (c : Fin J → ThinSpace m) (s : Fin J → Finset (Fin N))
    (hr : ∀ j, 0 < r j) (hε : ∀ j, 0 < ε j) (hεr : ∀ j, ε j ≤ r j/10)
    (hrδ : ∀ j, r j ≤ δ^3/4) (hεδ : ∀ j, ε j ≤ δ^4/4) (hc : ∀ j, (c j).2=0)
    (hsub : ∀ j, thinClosedBallAt (r j) (c j) ⊆ thinBallAt R 0)
    (hdis : Pairwise (fun i j => Disjoint (thinBallAt (r i) (c i)) (thinBallAt (r j) (c j))))
    {p : Space 3} (hp : radius (p,(0 : ThinSpace m))=δ^4) (ht : (p 0-1)^2 ≤ (δ^2)^2)
    (hv : ∀ j l, l ∈ s j → (∑ k, (v l k)^2) ≤ 1/16)
    (haxis : ∀ j l, l ∈ s j → ‖(c j).1-outputAxis δ (a l) (v l) p‖ ≤ δ^3/8) :
    (∑ j, thinLowerConstant m*(r j)^m*(ε j)^(2*m+2)*
      (outputDensityScale m δ*(∑ l ∈ s j, weights l))^(((m : ℝ)+1)/m)*
        Real.log (r j/ε j)) ≤
      thinValueRealAt R 0 (thinSlice (currentDensity (kakeyaPacketFamily δ a v weights)) p) := by
  have hp0 : 0 < radius (p,(0 : ThinSpace m)) := hp ▸ pow_pos hδ 4
  apply thinValueRealAt_localized_thin_lower hm hR 0 r ε
    (fun j => outputDensityScale m δ*(∑ l ∈ s j, weights l)) c hr hε hεr
    (fun j => mul_nonneg (outputDensityScale_pos m hδ).le
      (Finset.sum_nonneg (fun l _ => hw l))) hsub hdis
    (kakeyaPacketFamily_density_slice_smooth hδ a v weights hp0)
    (fun z _ => kakeyaPacketFamily_density_nonneg hδ a v hw (show 0 < radius (p,z) from hp0))
  intro j z hz
  have hP : ‖z.2‖^2 ≤ (δ^4)^2/16 := by
    have hzP : ‖z.2‖ < ε j := by simpa only [mem_ball,hc j,dist_zero_right] using hz.2
    nlinarith [hεδ j,norm_nonneg z.2,pow_pos hδ 4]
  exact kakeyaPacketFamily_output_density_lower hδ hδ1 a v hw (s j)
    (show radius (p,z)=δ^4 from hp) ht hP (hv j)
    (fun l hl => output_core_error hδ (a l) (v l) p (c j) (hrδ j) (haxis j l hl) hz)

end KakeyaSharp.Packet
