/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Definitions

@[expose] public section

/-! The actual logarithmic test function from the thin-source argument.
This file checks its sign, boundary values, core depth and smoothness.
The actual quaternionic Hessian and its determinant bound are checked in
`ThinHessian.lean` and `ThinDeterminant.lean`. -/

noncomputable section
open scoped ContDiff
namespace KakeyaSharp

abbrev ThinTransverseSpace (m : ℕ) := EuclideanSpace ℝ (Fin m × Fin 2)

abbrev ThinSpace (m : ℕ) := Space m × ThinTransverseSpace m

def thinNumerator {m : ℕ} (η : ℝ) (z : ThinSpace m) : ℝ :=
  η ^ 2 + ‖z.2‖ ^ 2

def thinDenominator {m : ℕ} (η : ℝ) (z : ThinSpace m) : ℝ :=
  η ^ 2 + 1 - ‖z.1‖ ^ 2

def thinProfile {m : ℕ} (η : ℝ) (z : ThinSpace m) : ℝ :=
  Real.log (thinNumerator η z / thinDenominator η z)

lemma thinNumerator_pos {m : ℕ} {η : ℝ} (hη : 0 < η) (z : ThinSpace m) :
    0 < thinNumerator η z := by
  unfold thinNumerator
  positivity

lemma thinDenominator_pos {m : ℕ} {η : ℝ} (hη : 0 < η) {z : ThinSpace m}
    (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) : 0 < thinDenominator η z := by
  unfold thinDenominator
  nlinarith [sq_pos_of_pos hη, sq_nonneg ‖z.2‖]

theorem thinProfile_nonpos {m : ℕ} {η : ℝ} (hη : 0 < η) {z : ThinSpace m}
    (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) : thinProfile η z ≤ 0 := by
  have hb := thinNumerator_pos hη z
  have hd := thinDenominator_pos hη hz
  apply Real.log_nonpos (div_nonneg hb.le hd.le)
  apply (div_le_one hd).mpr
  dsimp [thinNumerator, thinDenominator]
  linarith

theorem thinProfile_boundary {m : ℕ} {η : ℝ} (hη : 0 < η) {z : ThinSpace m}
    (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 = 1) : thinProfile η z = 0 := by
  have he : thinNumerator η z = thinDenominator η z := by
    dsimp [thinNumerator, thinDenominator]
    linarith
  unfold thinProfile
  rw [he, div_self (thinDenominator_pos hη hz.le).ne', Real.log_one]

/-- On the thin source, the depth is at least one full logarithm. -/
theorem thinProfile_core_depth {m : ℕ} {η : ℝ} (hη : 0 < η) (hη10 : η ≤ 1 / 10)
    {z : ThinSpace m} (hx : ‖z.1‖ ≤ 1 / 2) (hp : ‖z.2‖ ≤ η) :
    Real.log (1 / η) ≤ -thinProfile η z := by
  have hx2 : ‖z.1‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg z.1]
  have hp2 : ‖z.2‖ ^ 2 ≤ η ^ 2 := sq_le_sq₀ (norm_nonneg _) hη.le |>.mpr hp
  have hb := thinNumerator_pos hη z
  have hd : 0 < thinDenominator η z := by
    dsimp [thinDenominator]
    nlinarith [sq_nonneg η]
  have hbd : thinNumerator η z ≤ η * thinDenominator η z := by
    have hden : 3 / 4 ≤ thinDenominator η z := by
      dsimp [thinDenominator]
      nlinarith [sq_nonneg η]
    have h1 : thinNumerator η z ≤ 2 * η ^ 2 := by
      dsimp [thinNumerator]
      linarith
    have h2 : 2 * η ^ 2 ≤ η * (3 / 4) := by
      nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hη10)]
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hden hη.le))
  have hratio : thinNumerator η z / thinDenominator η z ≤ η :=
    (div_le_iff₀ hd).mpr hbd
  have hlog := Real.log_le_log (div_pos hb hd) hratio
  change thinProfile η z ≤ Real.log η at hlog
  rw [one_div, Real.log_inv]
  linarith

theorem thinProfile_smooth {m : ℕ} {η : ℝ} (hη : 0 < η) {z : ThinSpace m}
    (hz : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 1) :
    ContDiffAt ℝ ∞ (thinProfile η) z := by
  have hb := thinNumerator_pos hη z
  have hd := thinDenominator_pos hη hz
  have hn : ContDiffAt ℝ ∞ (thinNumerator η) z := by
    unfold thinNumerator
    exact contDiffAt_const.add (contDiffAt_snd.norm_sq (𝕜 := ℝ))
  have hdn : ContDiffAt ℝ ∞ (thinDenominator η) z := by
    unfold thinDenominator
    exact contDiffAt_const.sub (contDiffAt_fst.norm_sq (𝕜 := ℝ))
  exact (hn.div hdn hd.ne').log (div_pos hb hd).ne'

end KakeyaSharp
