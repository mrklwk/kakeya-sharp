/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.InputDomination

@[expose] public section

/-! A quantitative lower bound for the actual packet density in the
thin output region. The cutoff is the fixed normalized cutoff already used
by the input and propagation theorems. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set MeasureTheory

theorem ratio_norm_identity {m : ℕ} {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    ‖y.2.2‖^2 = (radius y)^2 * ∑ j, ((ratioRe y j)^2+(ratioIm y j)^2) := by
  have h := physical_transverse_distance hy (fun _ => 0)
  simpa only [mul_zero,sub_zero,EuclideanSpace.real_norm_sq_eq,
    Fintype.sum_prod_type,Fin.sum_univ_two] using h

theorem output_phase_le_half {m : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : radius y=h)
    (hv : (∑ j, (v j)^2) ≤ 1/16)
    (hx : (∑ j, (y.2.1 j-a j-time y*v j)^2) ≤ r*h/16)
    (hP : ‖y.2.2‖^2 ≤ h^2/16) :
    physicalPhase r a v y ≤ h/2 := by
  have hypos : 0 < radius y := hy ▸ hh
  have hnorm := ratio_norm_identity hypos
  rw [hy] at hnorm
  have hab : (∑ j, ((ratioRe y j)^2+(ratioIm y j)^2)) ≤ 1/16 := by
    apply le_of_mul_le_mul_left (a := h^2) _ (sq_pos_of_pos hh)
    nlinarith [hnorm,hP]
  have hvec : (∑ j, ((ratioRe y j-v j)^2+(ratioIm y j)^2)) ≤ 1/4 := by
    have hle : (∑ j, ((ratioRe y j-v j)^2+(ratioIm y j)^2)) ≤
        2*(∑ j, ((ratioRe y j)^2+(ratioIm y j)^2))+2*(∑ j, (v j)^2) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (ratioRe y j+v j),sq_nonneg (ratioIm y j)]
    linarith
  have hxdiv : (∑ j, (y.2.1 j-a j-time y*v j)^2)/(r+h) ≤ h/16 := by
    apply (div_le_iff₀ (add_pos hr hh)).mpr
    nlinarith [sq_nonneg h]
  have hmin := phase_minimum hr hh (time y) a v (fun j => y.2.1 j)
    (ratioRe y) (ratioIm y) v
  have he : energy r h (time y) a v (fun j => y.2.1 j) (ratioRe y) (ratioIm y) v =
      (∑ j, (y.2.1 j-a j-time y*v j)^2)/(r+h)+
        h*(∑ j, ((ratioRe y j-v j)^2+(ratioIm y j)^2)) := by
    simp only [energy,scalarEnergy,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,
      zero_add,Finset.sum_add_distrib,Finset.sum_div]
    simp only [← Finset.mul_sum]
    ring
  rw [he] at hmin
  change phase r (radius y) (time y) a v (fun j => y.2.1 j) (ratioRe y) (ratioIm y) ≤ h/2
  rw [hy]
  nlinarith [mul_le_mul_of_nonneg_left hvec hh.le]

theorem output_cutoff_eq_one {m : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : radius y=h)
    (hv : (∑ j, (v j)^2) ≤ 1/16)
    (hx : (∑ j, (y.2.1 j-a j-time y*v j)^2) ≤ r*h/16)
    (hP : ‖y.2.2‖^2 ≤ h^2/16) :
    standardCutoff (physicalPhase r a v y/h)=1 := by
  apply standardCutoff_eq_one
  have h := output_phase_le_half hr hh a v hy hv hx hP
  exact (div_le_iff₀ hh).mpr (by linarith)

theorem output_prefactor_lower (m : ℕ) {r h τ : ℝ} (hr : 0 < r) (hh : 0 < h)
    (hhr : h ≤ r) (ht : τ^2 ≤ r^2) :
    (5*h^2*r^2)^(-(m : ℝ)/2) ≤ prefactor m r h τ := by
  apply Real.rpow_le_rpow_of_nonpos
    (mul_pos (sq_pos_of_pos hh) (denominator_pos hr hh τ))
  · unfold denominator
    have hd : (r+h)^2+τ^2 ≤ 5*r^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg h)]
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m)) (by norm_num)

def outputDensityScale (m : ℕ) (δ : ℝ) : ℝ :=
  (5*(δ^4)^2*(δ^2)^2)^(-(m : ℝ)/2)/((δ^4)^m*cutoffMass m standardCutoff)

theorem outputDensityScale_pos (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < outputDensityScale m δ :=
  div_pos (Real.rpow_pos_of_pos (by positivity) _)
    (mul_pos (pow_pos (pow_pos hδ 4) m) (standardCutoff_mass_pos m))

/-- Every selected packet contributes its full weight on the displayed
thin region. The statement uses the actual normalized finite-family density. -/
theorem kakeyaPacketFamily_output_density_lower {m N : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (a v : Fin N → Fin m → ℝ)
    {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l) (s : Finset (Fin N))
    {y : ThinCurrentSpace m} (hy : radius y=δ^4) (ht : (time y)^2 ≤ (δ^2)^2)
    (hP : ‖y.2.2‖^2 ≤ (δ^4)^2/16)
    (hv : ∀ l ∈ s, (∑ j, (v l j)^2) ≤ 1/16)
    (hx : ∀ l ∈ s, (∑ j, (y.2.1 j-δ^2*a l j-time y*v l j)^2) ≤ δ^2*δ^4/16) :
    outputDensityScale m δ*(∑ l ∈ s, weights l) ≤
      currentDensity (kakeyaPacketFamily δ a v weights) y := by
  have hh := pow_pos hδ 4
  have hr := pow_pos hδ 2
  have hypos : 0 < radius y := hy ▸ hh
  have hden : 0 < (δ^4)^m*cutoffMass m standardCutoff :=
    mul_pos (pow_pos hh m) (standardCutoff_mass_pos m)
  have hhr : δ^4 ≤ δ^2 := by nlinarith [pow_le_one₀ hδ.le hδ1 (n := 2),sq_nonneg (δ^2)]
  have hlow := output_prefactor_lower m hr hh hhr ht
  rw [kakeyaPacketFamily_density_formula hδ a v weights,Finset.mul_sum]
  calc
    _ ≤ ∑ l ∈ s, (weights l/((δ^4)^m*cutoffMass m standardCutoff))*
        packetWeight (δ^2) (δ^4) (fun j => δ^2*a l j) (v l) standardCutoff y := by
      apply Finset.sum_le_sum
      intro l hl
      rw [packetWeight,output_cutoff_eq_one hr hh _ _ hy (hv l hl) (hx l hl) hP,hy,mul_one]
      have h := mul_le_mul_of_nonneg_left hlow (div_nonneg (hw l) hden.le)
      unfold outputDensityScale
      convert h using 1; ring
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun l =>
      mul_nonneg (div_nonneg (hw l) hden.le)
        (mul_nonneg (prefactor_pos m hr hypos _).le (standardCutoff_nonneg _)))

end KakeyaSharp.Packet
