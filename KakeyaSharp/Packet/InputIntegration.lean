/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.InputCoordinates
public import KakeyaSharp.Packet.NormalKernel

@[expose] public section

/-! Integration of the input barrier determinant against a directional weight.
The normal integration is uniform in its scale and in the transverse orientation. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open MeasureTheory

def inputKernel (m : ℕ) (h a b : ℝ) (z : ThinSpace m) : ℝ :=
  (8 : ℝ)^m*h/(h+inputQuadratic a b z)^(m+1)

theorem inputKernel_nonneg (m : ℕ) {h : ℝ} (hh : 0 < h) (a b : ℝ)
    (z : ThinSpace m) : 0 ≤ inputKernel m h a b z := by
  have := inputQuadratic_nonneg a b z
  unfold inputKernel
  positivity

theorem inputKernel_continuous (m : ℕ) {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    Continuous (inputKernel m h a b) := by
  unfold inputKernel
  apply Continuous.div continuous_const
    (((continuous_const.add (inputQuadratic_smooth m a b).continuous)).pow _)
  intro z
  exact pow_ne_zero _ (add_pos_of_pos_of_nonneg hh (inputQuadratic_nonneg a b z)).ne'

theorem inputAlpha_continuous {m : ℕ} (p : Space 3) : Continuous (inputAlpha (m := m) p) := by
  change Continuous (fun z : ThinSpace m => WithLp.toLp 2
    (fun j => (p 1*z.2 (j,0)+p 2*z.2 (j,1))/((p 1)^2+(p 2)^2)))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  apply Continuous.div_const
  fun_prop

theorem inputKernel_inputCoordinates_le {m : ℕ} {h a b : ℝ} (hh : 0 < h)
    (hab : a^2+b^2=1) (y : ThinSpace m) :
    inputKernel m h a b (inputCoordinates m a b hab y) ≤ (8 : ℝ)^m*normalKernel m h y.2 := by
  unfold inputKernel normalKernel
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_left (by positivity)
    (pow_pos (by positivity) _)
  exact pow_le_pow_left₀ (by positivity)
    (by linarith [norm_sq_le_inputQuadratic_inputCoordinates hab y]) _

theorem input_weighted_integrable {m : ℕ} (hm : 1 ≤ m) {h : ℝ} (hh : 0 < h)
    {p : Space 3} (hp : (p 1)^2+(p 2)^2=1) {B : Space m → ℝ}
    (hBm : Measurable B) (hBi : Integrable B) (hB : ∀ α, 0 ≤ B α) :
    Integrable (fun z => B (inputAlpha p z)*inputKernel m h (p 1) (p 2) z) := by
  let F := inputCoordinates m (p 1) (p 2) hp
  have hmeas : Measurable (fun z => B (inputAlpha p z)*inputKernel m h (p 1) (p 2) z) :=
    (hBm.comp (inputAlpha_continuous p).measurable).mul
      (inputKernel_continuous m hh (p 1) (p 2)).measurable
  apply ((inputCoordinates_measurePreserving m hp).integrable_comp hmeas.aestronglyMeasurable).mp
  have hi := (hBi.mul_prod (normalKernel_integrable hm hh)).const_mul ((8 : ℝ)^m)
  apply hi.mono' ((hmeas.comp F.continuous.measurable).aestronglyMeasurable)
  apply ae_of_all
  intro y
  change ‖B (inputAlpha p (F y))*inputKernel m h (p 1) (p 2) (F y)‖ ≤
    (8 : ℝ)^m*(B y.1*normalKernel m h y.2)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hB _) (inputKernel_nonneg m hh _ _ _))]
  change B (inputAlpha p (inputCoordinates m (p 1) (p 2) hp y))*_ ≤ _
  rw [inputAlpha_inputCoordinates hp]
  exact (mul_le_mul_of_nonneg_left (inputKernel_inputCoordinates_le hh hp y) (hB y.1)).trans_eq (by ring)

theorem input_weighted_integral_le {m : ℕ} (hm : 1 ≤ m) {h : ℝ} (hh : 0 < h)
    {p : Space 3} (hp : (p 1)^2+(p 2)^2=1) {B : Space m → ℝ}
    (hBm : Measurable B) (hBi : Integrable B) (hB : ∀ α, 0 ≤ B α) :
    (∫ z, B (inputAlpha p z)*inputKernel m h (p 1) (p 2) z) ≤
      ((8 : ℝ)^m*normalMass m)*(∫ α, B α) := by
  let F := inputCoordinates m (p 1) (p 2) hp
  have hi := input_weighted_integrable hm hh hp hBm hBi hB
  rw [← (inputCoordinates_measurePreserving m hp).integral_comp
    F.toHomeomorph.measurableEmbedding]
  have hc := (inputCoordinates_measurePreserving m hp).integrable_comp_of_integrable hi
  have hj := (hBi.mul_prod (normalKernel_integrable hm hh)).const_mul ((8 : ℝ)^m)
  have hle := integral_mono hc hj (fun y => by
    change B (inputAlpha p (F y))*_ ≤ (8 : ℝ)^m*(B y.1*normalKernel m h y.2)
    change B (inputAlpha p (inputCoordinates m (p 1) (p 2) hp y))*_ ≤ _
    rw [inputAlpha_inputCoordinates hp]
    exact (mul_le_mul_of_nonneg_left (inputKernel_inputCoordinates_le hh hp y)
      (hB y.1)).trans_eq (by ring))
  apply hle.trans
  rw [integral_const_mul]
  change (8 : ℝ)^m*(∫ y : Space m × ThinTransverseSpace m,
    B y.1*normalKernel m h y.2 ∂(volume.prod volume)) ≤ _
  rw [integral_prod_mul]
  have hb : 0 ≤ ∫ α, B α := integral_nonneg hB
  have hn := mul_le_mul_of_nonneg_left (normalKernel_integral_le hm hh)
    (mul_nonneg (by positivity : 0 ≤ (8 : ℝ)^m) hb)
  nlinarith

end KakeyaSharp.Packet
