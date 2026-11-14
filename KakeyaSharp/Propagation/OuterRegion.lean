/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import OAI.Analysis.PDE.Concentration.OuterTrace

@[expose] public section

/-! The fixed outer comparison, localized also in the time coordinate.
The constants are independent of the small inner radius. -/
noncomputable section
set_option maxHeartbeats 800000
namespace KakeyaSharp.Propagation
open OAI.Analysis.PDE.Concentration MeasureTheory Set Metric Filter Laplacian InnerProductSpace
open scoped ContDiff Topology

def outerBox : Set CylinderSpace :=
  {x | x 0 ∈ Ioo (-cylinderTimeEnd-1) (cylinderTimeEnd+1) ∧ x ∈ outerAnnulus}

theorem outerBox_isOpen : IsOpen outerBox :=
  (isOpen_Ioo.preimage (by fun_prop : Continuous (fun x : CylinderSpace => x 0))).inter
    isOpen_outerAnnulus

theorem shell_subset_outerBox :
    cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 3 ⊆ outerBox := by
  intro x hx
  have ht : x 0 ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd := hx.1
  exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
    ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩⟩

theorem outerBox_ball_subset {x : CylinderSpace}
    (hx : x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2) :
    closedBall x (7*(1/64)) ⊆ outerBox := by
  intro y hy
  have ht : x 0 ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd := hx.1
  have hdist : dist y x ≤ 7*(1/64) := hy
  have he : |y 0-x 0| ≤ dist y x := by
    simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (y-x) (0 : Fin 3)
  exact ⟨⟨by linarith [(abs_le.mp he).1,ht.1],
    by linarith [(abs_le.mp he).2,ht.2]⟩, outerShell_ball_subset hx hy⟩

theorem exists_outerBox_mixing_constant : ∃ M : ℝ, 0 < M ∧
    ∀ f : CylinderSpace → ℝ, ContDiffOn ℝ ∞ f outerBox →
      (∀ y ∈ outerBox, 0 ≤ f y) → (∀ y ∈ outerBox, Δ f y ≤ 0) →
      ∀ x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2,
        (∫ y in cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2, f y) ≤ M*f x := by
  let K : Set (ℝ × ℝ × ℝ) := Icc (-cylinderTimeEnd) cylinderTimeEnd ×ˢ
    (Icc 1 2 ×ˢ Icc (-Real.pi) Real.pi)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hconv : Convex ℝ K := (convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))
  have he := cylinderShell_eq_image (t₀ := -cylinderTimeEnd) (t₁ := cylinderTimeEnd)
    (a := 1) (b := 2) (by norm_num)
  obtain ⟨M,hM,hm⟩ := exists_uniform_local_compact_volume_mixing hK hconv
    contDiff_cylinderPoint.continuous.continuousOn (show (0 : ℝ) < 1/64 by norm_num)
    outerBox_isOpen (fun x hx => outerBox_ball_subset (by rw [he]; exact hx))
  refine ⟨M,hM,?_⟩
  intro f hf hn hΔ x hx
  rw [he] at hx ⊢
  exact hm f hf hn hΔ x hx

theorem exists_outerBox_trace_constant : ∃ D : ℝ, 0 < D ∧
    ∀ f : CylinderSpace → ℝ, ContDiffOn ℝ ∞ f outerBox →
      (∀ y ∈ outerBox, 0 ≤ f y) → (∀ y ∈ outerBox, Δ f y ≤ 0) →
      ∀ x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2,
        cylinderAverage f 1 ≤ D*f x := by
  obtain ⟨C,hC,htrace⟩ := exists_cylinder_trace_volume_constant
  obtain ⟨M,hM,hmix⟩ := exists_outerBox_mixing_constant
  refine ⟨C*M,mul_pos hC hM,?_⟩
  intro f hf hn hΔ
  let K := cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 3
  have hK : IsCompact K := isCompact_cylinderShell _ _ _ _
  have hKU : K ⊆ outerBox := shell_subset_outerBox
  obtain ⟨F,hF,he⟩ := exists_global_smooth_eq_near_closed hK.isClosed outerBox_isOpen hKU hf
  have hpoint {t r θ : ℝ} (ht : t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd)
      (hr : r ∈ Icc (1 : ℝ) 3) :
      F (cylinderPoint t r θ)=f (cylinderPoint t r θ) :=
    (he _ (cylinderPoint_mem_shell ht hr (by linarith [hr.1]))).self_of_nhds
  have havg : cylinderAverage F 1=cylinderAverage f 1 :=
    cylinderAverage_congr (fun t ht θ _ => hpoint ht ⟨le_rfl,by norm_num⟩)
  have hsmall : cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2 ⊆ K := by
    intro x hx
    exact ⟨hx.1,hx.2.1,by linarith [hx.2.2]⟩
  have hint : (∫ x in cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2, F x)=
      ∫ x in cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2, f x :=
    setIntegral_congr_fun (isCompact_cylinderShell _ _ _ _).measurableSet
      (fun x hx => (he x (hsmall hx)).self_of_nhds)
  have hb := htrace F hF
    (fun x hx => by rw [(he x hx).self_of_nhds]; exact hn x (hKU hx))
    (fun x hx => by
      rw [(laplacian_congr_nhds (he x hx)).self_of_nhds]
      exact hΔ x (hKU hx))
  rw [havg,hint] at hb
  intro x hx
  exact hb.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hmix f hf hn hΔ x hx) hC.le)

end KakeyaSharp.Propagation
