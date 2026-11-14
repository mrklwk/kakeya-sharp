/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Physical

@[expose] public section

/-! Quantitative bounds on packet support in the original spatial
coordinates. These estimates follow from the actual minimized phase. -/
noncomputable section
namespace KakeyaSharp.Packet

theorem phase_deviation_bounds {m : ℕ} {r s L : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ : ℝ) (a v x α β : Fin m → ℝ) (hL : phase r s τ a v x α β ≤ L) :
    (∑ j, (center r s τ (a j) (v j) (x j) (α j)-v j)^2) ≤ L/r ∧
    (∑ j, (residual r s τ (a j) (v j) (x j) (α j))^2) ≤ L/(r+s) ∧
    (∑ j, (α j-center r s τ (a j) (v j) (x j) (α j))^2) ≤ L/s ∧
    (∑ j, (β j)^2) ≤ L/s := by
  obtain ⟨hc,hd,hα,hβ⟩ := phase_controls_deviations hr hs τ a v x α β
  exact ⟨(le_div_iff₀ hr).mpr (by nlinarith),
    (le_div_iff₀ (add_pos hr hs)).mpr (by nlinarith),
    (le_div_iff₀ hs).mpr (by nlinarith), (le_div_iff₀ hs).mpr (by nlinarith)⟩

theorem phase_controls_x_distance {m : ℕ} {r s L : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ : ℝ) (a v x α β : Fin m → ℝ) (hL : phase r s τ a v x α β ≤ L) :
    (∑ j, (x j-a j-τ*v j)^2) ≤ 2*L*(τ^2/r+(r+s)) := by
  obtain ⟨hc,hd,_,_⟩ := phase_deviation_bounds hr hs τ a v x α β hL
  calc
    _ ≤ ∑ j, (2*τ^2*(center r s τ (a j) (v j) (x j) (α j)-v j)^2+
        2*(r+s)^2*(residual r s τ (a j) (v j) (x j) (α j))^2) := by
      apply Finset.sum_le_sum
      intro j _
      have he := (center_equations hr hs τ (a j) (v j) (x j) (α j)).2
      have he' : x j-a j-τ*v j =
          τ*(center r s τ (a j) (v j) (x j) (α j)-v j)+
            (r+s)*residual r s τ (a j) (v j) (x j) (α j) := by linarith
      rw [he']
      nlinarith [sq_nonneg (τ*(center r s τ (a j) (v j) (x j) (α j)-v j)-
        (r+s)*residual r s τ (a j) (v j) (x j) (α j))]
    _ = 2*τ^2*(∑ j, (center r s τ (a j) (v j) (x j) (α j)-v j)^2)+
        2*(r+s)^2*(∑ j, (residual r s τ (a j) (v j) (x j) (α j))^2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2*τ^2*(L/r)+2*(r+s)^2*(L/(r+s)) := by gcongr
    _ = _ := by field_simp

theorem phase_controls_ratio_distance {m : ℕ} {r s L : ℝ} (hr : 0 < r) (hs : 0 < s)
    (τ : ℝ) (a v x α β : Fin m → ℝ) (hL : phase r s τ a v x α β ≤ L) :
    (∑ j, ((α j-v j)^2+(β j)^2)) ≤ 2*L/r+3*L/s := by
  obtain ⟨hc,_,hα,hβ⟩ := phase_deviation_bounds hr hs τ a v x α β hL
  calc
    _ ≤ ∑ j, (2*(α j-center r s τ (a j) (v j) (x j) (α j))^2+
        2*(center r s τ (a j) (v j) (x j) (α j)-v j)^2+(β j)^2) := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (α j-2*center r s τ (a j) (v j) (x j) (α j)+v j)]
    _ = 2*(∑ j, (α j-center r s τ (a j) (v j) (x j) (α j))^2)+
        2*(∑ j, (center r s τ (a j) (v j) (x j) (α j)-v j)^2)+(∑ j, (β j)^2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2*(L/s)+2*(L/r)+L/s := by gcongr
    _ = _ := by ring

theorem ratio_reconstruction {m : ℕ} {y : ThinCurrentSpace m}
    (hy : 0 < radius y) (j : Fin m) :
    y.2.2 (j,0)=y.1 1*ratioRe y j-y.1 2*ratioIm y j ∧
    y.2.2 (j,1)=y.1 2*ratioRe y j+y.1 1*ratioIm y j := by
  have hQ : (y.1 1)^2+(y.1 2)^2 ≠ 0 := (Real.sqrt_pos.mp hy).ne'
  constructor <;> unfold ratioRe ratioIm <;> field_simp <;> ring

theorem physical_transverse_distance {m : ℕ} {y : ThinCurrentSpace m}
    (hy : 0 < radius y) (v : Fin m → ℝ) :
    (∑ j, ((y.2.2 (j,0)-y.1 1*v j)^2+(y.2.2 (j,1)-y.1 2*v j)^2)) =
      (radius y)^2*(∑ j, ((ratioRe y j-v j)^2+(ratioIm y j)^2)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨h₀,h₁⟩ := ratio_reconstruction hy j
  conv_lhs => rw [h₀,h₁]
  rw [radius_sq]
  ring

theorem physicalPhase_controls_distance {m : ℕ} {r L : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (hL : physicalPhase r a v y ≤ L) :
    (∑ j, (y.2.1 j-a j-time y*v j)^2) ≤ 2*L*((time y)^2/r+r+radius y) ∧
    (∑ j, ((y.2.2 (j,0)-y.1 1*v j)^2+(y.2.2 (j,1)-y.1 2*v j)^2)) ≤
      L*(2*(radius y)^2/r+3*radius y) := by
  constructor
  · simpa only [add_assoc] using phase_controls_x_distance hr hy (time y) a v
      (fun j => y.2.1 j) (ratioRe y) (ratioIm y) hL
  · rw [physical_transverse_distance hy]
    calc
      _ ≤ (radius y)^2*(2*L/r+3*L/radius y) :=
        mul_le_mul_of_nonneg_left (phase_controls_ratio_distance hr hy (time y) a v
          (fun j => y.2.1 j) (ratioRe y) (ratioIm y) hL) (sq_nonneg _)
      _ = _ := by field_simp

theorem rawPacket_ne_zero_phase_le {m : ℕ} {r h M : ℝ} (hh : 0 < h)
    (a v : Fin m → ℝ) {χ : ℝ → ℝ} (hχ : ∀ u, M < u → χ u=0)
    {y : ThinCurrentSpace m} (hA : rawPacket r h a v χ y ≠ 0) :
    physicalPhase r a v y ≤ h*M := by
  by_contra hn
  have hcut : χ (physicalPhase r a v y/h)=0 := hχ _ ((lt_div_iff₀ hh).mpr (by linarith))
  apply hA
  simp only [rawPacket, packetWeight, hcut, mul_zero, zero_smul]

def supportBound {m : ℕ} (r L : ℝ) (a v : Fin m → ℝ) (p : Space 3) : ℝ :=
  let s := radius (p, (0 : ThinSpace m))
  let τ := p 0-1
  4*(∑ j, (a j)^2)+(4*τ^2+2*s^2)*(∑ j, (v j)^2)+
    L*(4*(τ^2/r+r+s)+4*s^2/r+6*s)

theorem physicalPhase_controls_spatial_norm {m : ℕ} {r L : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (hL : physicalPhase r a v y ≤ L) :
    ‖y.2.1‖^2+‖y.2.2‖^2 ≤ supportBound r L a v y.1 := by
  obtain ⟨hx,hP⟩ := physicalPhase_controls_distance hr a v hy hL
  have hxx : (∑ j, (y.2.1 j)^2) ≤
      2*(∑ j, (y.2.1 j-a j-time y*v j)^2)+4*(∑ j, (a j)^2)+
        4*(time y)^2*(∑ j, (v j)^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (y.2.1 j-2*(a j+time y*v j)), sq_nonneg (a j-time y*v j)]
  have hPP : (∑ j, ((y.2.2 (j,0))^2+(y.2.2 (j,1))^2)) ≤
      2*(∑ j, ((y.2.2 (j,0)-y.1 1*v j)^2+(y.2.2 (j,1)-y.1 2*v j)^2))+
        2*(radius y)^2*(∑ j, (v j)^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    rw [radius_sq]
    nlinarith [sq_nonneg (y.2.2 (j,0)-2*y.1 1*v j), sq_nonneg (y.2.2 (j,1)-2*y.1 2*v j)]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  change _ ≤ 4*(∑ j, (a j)^2)+(4*(time y)^2+2*(radius y)^2)*(∑ j, (v j)^2)+
    L*(4*((time y)^2/r+r+radius y)+4*(radius y)^2/r+6*radius y)
  linear_combination 2*hx+2*hP+hxx+hPP

theorem rawPacket_eq_zero_of_supportBound {m : ℕ} {r h M R : ℝ}
    (hr : 0 < r) (hh : 0 < h) (a v : Fin m → ℝ)
    {χ : ℝ → ℝ} (hχ : ∀ u, M < u → χ u=0)
    {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (hbound : supportBound r (h*M) a v y.1 < R^2)
    (hfar : R^2 ≤ ‖y.2.1‖^2+‖y.2.2‖^2) : rawPacket r h a v χ y = 0 := by
  by_contra hne
  have hp := rawPacket_ne_zero_phase_le hh a v hχ hne
  have hn := physicalPhase_controls_spatial_norm hr a v hy hp
  linarith

theorem supportBound_uniform {m : ℕ} {δ M A V : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (b v : Fin m → ℝ) (hb : (∑ j, (b j)^2) ≤ A)
    (hv : (∑ j, (v j)^2) ≤ V) (p : Space 3)
    (ht : (p 0-1)^2 ≤ 16) (hs : radius (p, (0 : ThinSpace m)) ≤ 4) :
    supportBound (δ^2) (δ^4*M) (fun j => δ^2*b j) v p ≤
      4*δ^4*A+96*V+172*M*δ^2 := by
  let s := radius (p, (0 : ThinSpace m))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs4 : s ≤ 4 := hs
  have hs2 : s^2 ≤ 16 := by nlinarith
  have hd2 : δ^2 ≤ 1 := by nlinarith
  have hd4 : δ^4 ≤ 1 := by nlinarith [sq_nonneg (δ^2-1)]
  have hA : 0 ≤ A := le_trans (Finset.sum_nonneg (fun j _ => sq_nonneg (b j))) hb
  have hV : 0 ≤ V := le_trans (Finset.sum_nonneg (fun j _ => sq_nonneg (v j))) hv
  have he : supportBound (δ^2) (δ^4*M) (fun j => δ^2*b j) v p =
      4*δ^4*(∑ j, (b j)^2)+(4*(p 0-1)^2+2*s^2)*(∑ j, (v j)^2)+
        M*δ^2*(4*(p 0-1)^2+4*δ^4+10*δ^2*s+4*s^2) := by
    unfold supportBound
    simp only [mul_pow, ← Finset.mul_sum]
    dsimp only [s]
    have hd := hδ.ne'
    field_simp
    ring
  rw [he]
  have hh : 4*(p 0-1)^2+4*δ^4+10*δ^2*s+4*s^2 ≤ 172 := by
    have hds : δ^2*s ≤ 4 := (mul_le_mul_of_nonneg_right hd2 hs0).trans (by simpa using hs4)
    nlinarith
  calc
    _ ≤ 4*δ^4*A+96*V+(M*δ^2)*172 := by
      gcongr
      · nlinarith
    _ = _ := by ring

end KakeyaSharp.Packet
