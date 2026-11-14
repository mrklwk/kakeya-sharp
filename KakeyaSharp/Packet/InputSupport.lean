/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.InputBarrier
public import KakeyaSharp.Packet.KakeyaFamily

@[expose] public section

/-! Support at time zero and unit transverse radius. The normal width is
delta squared, while the directional width is delta. -/
noncomputable section
set_option maxHeartbeats 800000
namespace KakeyaSharp.Packet
open Set MeasureTheory

theorem radius_eq_one_of_unit {m : ℕ} {p : Space 3}
    (hp : (p 1)^2+(p 2)^2=1) (z : ThinSpace m) : radius (p,z)=1 := by
  simp only [radius, hp, Real.sqrt_one]

theorem phase_controls_input_normal {m : ℕ} {r L : ℝ} (hr : 0 < r)
    (a v x α β : Fin m → ℝ) (hL : phase r 1 (-1) a v x α β ≤ L) :
    (∑ j, ((x j+α j)^2+2*(β j)^2)) ≤
      3*(∑ j, (a j)^2)+(3*r+8)*L := by
  obtain ⟨_,hd,hα,hβ⟩ := phase_deviation_bounds hr (show (0 : ℝ) < 1 by norm_num)
    (-1) a v x α β hL
  simp only [div_one] at hα hβ
  have hs : (∑ j, (x j+α j)^2) ≤
      3*(∑ j, (a j)^2)+3*(r+1)^2*(∑ j, (residual r 1 (-1) (a j) (v j) (x j) (α j))^2)+
      3*(∑ j, (α j-center r 1 (-1) (a j) (v j) (x j) (α j))^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have he := (center_equations hr (show (0 : ℝ) < 1 by norm_num)
      (-1) (a j) (v j) (x j) (α j)).2
    let c := center r 1 (-1) (a j) (v j) (x j) (α j)
    let d := residual r 1 (-1) (a j) (v j) (x j) (α j)
    have hx : x j+α j = a j+(r+1)*d+(α j-c) := by dsimp [c,d]; linarith
    rw [hx]
    change (a j+(r+1)*d+(α j-c))^2 ≤ 3*(a j)^2+3*(r+1)^2*d^2+3*(α j-c)^2
    nlinarith [sq_nonneg (a j-(r+1)*d), sq_nonneg (a j-(α j-c)),
      sq_nonneg ((r+1)*d-(α j-c))]
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 3*(r+1)^2 by positivity)
  have he : 3*(r+1)^2*(L/(r+1))=3*(r+1)*L := by field_simp
  rw [he] at hd'
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

theorem input_phase_support {m : ℕ} {δ A : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (a v : Fin m → ℝ)
    (ha : (∑ j, (a j)^2) ≤ A) {p : Space 3}
    (ht : p 0=0) (hp : (p 1)^2+(p 2)^2=1) (z : ThinSpace m)
    (hphase : physicalPhase (δ^2) (fun j => δ^2*a j) v (p,z) ≤ δ^4) :
    (∑ j, (ratioRe (p,z) j-v j)^2) ≤ 5*δ^2 ∧
      inputQuadratic (p 1) (p 2) z ≤ (3*A+11)*δ^4 := by
  have hr : 0 < δ^2 := pow_pos hδ 2
  have hd2 : δ^2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hd4 : δ^4 ≤ δ^2 := by nlinarith [sq_nonneg (δ^2-1)]
  have htime : time (p,z)=(-1) := by simp [time,ht]
  have hphase' : phase (δ^2) 1 (-1) (fun j => δ^2*a j) v
      (fun j => z.1 j) (ratioRe (p,z)) (ratioIm (p,z)) ≤ δ^4 := by
    simpa only [physicalPhase, radius_eq_one_of_unit hp z, htime] using hphase
  constructor
  · have hb := phase_controls_ratio_distance hr (show (0 : ℝ) < 1 by norm_num)
      (-1) (fun j => δ^2*a j) v (fun j => z.1 j) (ratioRe (p,z)) (ratioIm (p,z)) hphase'
    have hdrop : (∑ j, (ratioRe (p,z) j-v j)^2) ≤
        ∑ j, ((ratioRe (p,z) j-v j)^2+(ratioIm (p,z) j)^2) :=
      Finset.sum_le_sum (fun j _ => le_add_of_nonneg_right (sq_nonneg _))
    have he : δ^4/δ^2=δ^2 := by field_simp
    have hb' : 2*δ^4/δ^2+3*δ^4/1 ≤ 5*δ^2 := by rw [mul_div_assoc,he,div_one]; linarith
    exact hdrop.trans (hb.trans hb')
  · rw [inputQuadratic_eq_ratios hp]
    have hn := phase_controls_input_normal hr (fun j => δ^2*a j) v
      (fun j => z.1 j) (ratioRe (p,z)) (ratioIm (p,z)) hphase'
    have he : (∑ j, (δ^2*a j)^2)=δ^4*(∑ j, (a j)^2) := by
      simp only [mul_pow, ← Finset.mul_sum]
      congr 1
      ring
    rw [he] at hn
    have ha' := mul_le_mul_of_nonneg_left ha (pow_nonneg hδ.le 4)
    have hd := mul_le_mul_of_nonneg_right hd2 (pow_nonneg hδ.le 4)
    nlinarith

theorem input_cutoff_support {m : ℕ} {δ A : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (a v : Fin m → ℝ)
    (ha : (∑ j, (a j)^2) ≤ A) {p : Space 3}
    (ht : p 0=0) (hp : (p 1)^2+(p 2)^2=1) (z : ThinSpace m)
    (hcut : standardCutoff (physicalPhase (δ^2) (fun j => δ^2*a j) v (p,z)/δ^4) ≠ 0) :
    (∑ j, (ratioRe (p,z) j-v j)^2) ≤ 5*δ^2 ∧
      inputQuadratic (p 1) (p 2) z ≤ (3*A+11)*δ^4 := by
  apply input_phase_support hδ hδ1 a v ha ht hp z
  by_contra hn
  apply hcut
  apply standardCutoff_eq_zero
  apply (le_div_iff₀ (pow_pos hδ 4)).mpr
  linarith

theorem prefactor_input_le_one (m : ℕ) {r : ℝ} (_hr : 0 < r) :
    prefactor m r 1 (-1) ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · simp only [one_pow, one_mul, denominator]
    nlinarith [sq_nonneg (r+1)]
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m)) (by norm_num)

theorem standardCutoff_le_one (t : ℝ) : standardCutoff t ≤ 1 := Real.smoothTransition.le_one _

end KakeyaSharp.Packet
