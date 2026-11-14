/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.VariationalStructure

@[expose] public section

/-! Uniform source continuity, including at sources which vanish. -/
noncomputable section
namespace KakeyaSharp
open Set

theorem thinValueRealAt_add_constant_le {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) {A a : ℝ}
    (hA : 0 ≤ A) (ha : a ∈ Icc (0 : ℝ) 1)
    (hρA : ∀ z ∈ thinBallAt R o, ρ z ≤ A) :
    thinValueRealAt R o (fun z => ρ z+a) ≤ thinValueRealAt R o ρ +
      a * ((A+1)^(((m : ℝ)+1)/m) * thinValueRealAt R o (fun _ => 1)) := by
  have he : (fun z => ρ z+a) = (1-a)•ρ+a•(fun z => ρ z+1) := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hb : thinValueRealAt R o (fun z => ρ z+1) ≤
      (A+1)^(((m : ℝ)+1)/m) * thinValueRealAt R o (fun _ => 1) := by
    rw [← thinValueRealAt_smul hm hR o continuousOn_const (by linarith : 0 ≤ A+1)]
    apply thinValueRealAt_mono hm hR o (hρ.add continuousOn_const)
      (continuousOn_const.smul continuousOn_const)
    intro z hz
    change ρ z+1 ≤ (A+1)*1
    nlinarith [hρA z hz]
  rw [he]
  have hc := thinValueRealAt_convex hm hR o hρ
    (σ := fun z => ρ z+1) (hρ.add continuousOn_const) ha
  have hn := thinValueRealAt_nonneg hm hR o hρ
  have hmul := mul_le_mul_of_nonneg_left hb ha.1
  nlinarith [mul_nonneg ha.1 hn]

theorem thinValueRealAt_sub_le_of_source_close {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ σ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hσ : ContinuousOn σ (thinClosedBallAt R o)) {A a : ℝ}
    (hA : 0 ≤ A) (ha : a ∈ Icc (0 : ℝ) 1)
    (hσA : ∀ z ∈ thinBallAt R o, σ z ≤ A)
    (hclose : ∀ z ∈ thinBallAt R o, ρ z ≤ σ z+a) :
    thinValueRealAt R o ρ - thinValueRealAt R o σ ≤
      a * ((A+1)^(((m : ℝ)+1)/m) * thinValueRealAt R o (fun _ => 1)) := by
  have hmono := thinValueRealAt_mono hm hR o hρ
    (σ := fun z => σ z+a) (hσ.add continuousOn_const) hclose
  have hb := thinValueRealAt_add_constant_le hm hR o hσ hA ha hσA
  linarith

theorem thinValueRealAt_lipschitz_bound {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ σ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o))
    (hσ : ContinuousOn σ (thinClosedBallAt R o)) {A a : ℝ}
    (hA : 0 ≤ A) (ha : a ∈ Icc (0 : ℝ) 1)
    (hρA : ∀ z ∈ thinBallAt R o, ρ z ≤ A)
    (hσA : ∀ z ∈ thinBallAt R o, σ z ≤ A)
    (hclose : ∀ z ∈ thinBallAt R o, |ρ z-σ z| ≤ a) :
    |thinValueRealAt R o ρ - thinValueRealAt R o σ| ≤
      a * ((A+1)^(((m : ℝ)+1)/m) * thinValueRealAt R o (fun _ => 1)) := by
  apply abs_le.mpr
  constructor
  · have h := thinValueRealAt_sub_le_of_source_close hm hR o hσ hρ hA ha hρA
      (fun z hz => by have hh := (abs_le.mp (hclose z hz)).1; linarith)
    linarith
  · exact thinValueRealAt_sub_le_of_source_close hm hR o hρ hσ hA ha hσA
      (fun z hz => by have hh := (abs_le.mp (hclose z hz)).2; linarith)

open Filter
open scoped Topology

theorem thinValueRealAt_regularization {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : 0 < R) (o : ThinSpace m) {ρ : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : Tendsto ε l (𝓝 0)) (hε0 : ∀ᶠ i in l, 0 ≤ ε i) :
    Tendsto (fun i => thinValueRealAt R o (fun z => ρ z+ε i)) l (𝓝 (thinValueRealAt R o ρ)) := by
  obtain ⟨C,hC⟩ := (thinClosedBallAt_compact hR.le o).exists_bound_of_continuousOn hρ
  let A : ℝ := max C 0
  have hA : 0 ≤ A := le_max_right _ _
  have hbound : ∀ z ∈ thinBallAt R o, ρ z ≤ A := by
    intro z hz
    exact (le_abs_self _).trans ((hC z
      (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)).trans (le_max_left _ _))
  let M : ℝ := ((A+1)+1)^(((m : ℝ)+1)/m) * thinValueRealAt R o (fun _ => 1)
  have hsmall : ∀ᶠ i in l, ε i < 1 := hε.eventually (Iio_mem_nhds (by norm_num))
  have hb : ∀ᶠ i in l, |thinValueRealAt R o (fun z => ρ z+ε i) - thinValueRealAt R o ρ| ≤ ε i*M := by
    filter_upwards [hε0,hsmall] with i hi hi1
    apply thinValueRealAt_lipschitz_bound hm hR o (ρ := fun z => ρ z+ε i) (σ := ρ)
      (hρ.add continuousOn_const) hρ
      (show 0 ≤ A+1 by linarith) ⟨hi,hi1.le⟩
    · intro z hz
      linarith [hbound z hz]
    · intro z hz
      linarith [hbound z hz]
    · intro z _
      simp only [add_sub_cancel_left, abs_of_nonneg hi, le_refl]
  have hm0 : Tendsto (fun i => ε i*M) l (𝓝 0) := by simpa using hε.mul_const M
  have ht := squeeze_zero' (Eventually.of_forall (fun i => abs_nonneg
    (thinValueRealAt R o (fun z => ρ z+ε i) - thinValueRealAt R o ρ))) hb hm0
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq] using ht

end KakeyaSharp
