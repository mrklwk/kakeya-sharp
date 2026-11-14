/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Propagation.OuterRegion
public import OAI.Analysis.PDE.Concentration.LocalCylinder
public import OAI.Analysis.PDE.Concentration.TimeTrace

@[expose] public section

/-! Single-log cylinder propagation from a fixed outer radius.
This theorem is local in time and is presently stated for smooth functions.
The continuous weak-superharmonic limit is a separate remaining step. -/
noncomputable section
set_option maxHeartbeats 800000
namespace KakeyaSharp.Propagation
open OAI.Analysis.PDE.Concentration MeasureTheory Set Metric Filter Laplacian InnerProductSpace
open scoped ContDiff Topology

def cylinderDomain (ρ : ℝ) : Set CylinderSpace :=
  {x | x 0 ∈ Ioo (-cylinderTimeEnd-1) (cylinderTimeEnd+1) ∧
    ρ/2 < ‖(cylinderComplexEquiv x).2‖ ∧ ‖(cylinderComplexEquiv x).2‖ < 4}

theorem cylinderDomain_isOpen (ρ : ℝ) : IsOpen (cylinderDomain ρ) :=
  (isOpen_Ioo.preimage (by fun_prop : Continuous (fun x : CylinderSpace => x 0))).inter
    (isOpen_Ioo.preimage continuous_cylinderComplexCoordinate.norm)

theorem outerBox_subset_cylinderDomain {ρ : ℝ} (hρ : ρ < 1) :
    outerBox ⊆ cylinderDomain ρ := by
  intro x hx
  exact ⟨hx.1,by linarith [hx.2.1],hx.2.2⟩

theorem cylinderShell_subset_domain {ρ : ℝ} (hρ : 0 < ρ) :
    cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ 3 ⊆ cylinderDomain ρ := by
  intro x hx
  have ht : x 0 ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd := hx.1
  exact ⟨⟨by linarith [ht.1],by linarith [ht.2]⟩,
    by linarith [hx.2.1],by linarith [hx.2.2]⟩

/-- Only one logarithm is lost when the input point stays at transverse radius one.
The time interval and the outer region are fixed independently of the inner radius. -/
theorem exists_singleLog_cylinder_constant : ∃ C : ℝ, 0 < C ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ f : CylinderSpace → ℝ, ContDiffOn ℝ ∞ f (cylinderDomain ρ) →
      (∀ x ∈ cylinderDomain ρ, 0 ≤ f x) →
      (∀ x ∈ cylinderDomain ρ, Δ f x ≤ 0) → ∀ θ : ℝ,
      (∫ t in (1 : ℝ)..2, ∫ φ in (0 : ℝ)..(2*Real.pi), f (cylinderPoint t ρ φ)) ≤
        C*(1+|Real.log ρ|)*f (cylinderPoint 0 1 θ) := by
  obtain ⟨D,hD,houter⟩ := exists_outerBox_trace_constant
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C : ℝ := (8*D/Real.log 3)*(Real.log 3+1)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ρ hρ hρ1 f hf hn hΔ θ
  have hsub := outerBox_subset_cylinderDomain hρ1
  have hsource : cylinderPoint 0 1 θ ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2 :=
    cylinderPoint_mem_shell ⟨by linarith [cylinderTimeEnd_pos],by linarith [cylinderTimeEnd_pos]⟩
      ⟨le_rfl,by norm_num⟩ (by norm_num)
  have hsrc : 0 ≤ f (cylinderPoint 0 1 θ) := hn _ (hsub (shell_subset_outerBox
    ⟨hsource.1,hsource.2.1,by linarith [hsource.2.2]⟩))
  have ho := houter f (hf.mono hsub) (fun x hx => hn x (hsub hx))
    (fun x hx => hΔ x (hsub hx)) _ hsource
  have hpoint {r t φ : ℝ} (hr : r ∈ Icc ρ 3)
      (ht : t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd) :
      cylinderPoint t r φ ∈ cylinderDomain ρ :=
    cylinderShell_subset_domain hρ (cylinderPoint_mem_shell ht hr (hρ.le.trans hr.1))
  have hr := cylinderAverage_logarithmic_lower_on (cylinderDomain_isOpen ρ) hf hρ hρ1
    (fun _ hr _ ht _ _ => hpoint hr ht)
    (fun _ hr _ ht _ _ => hn _ (hpoint hr ht))
    (fun _ hr _ ht _ _ => hΔ _ (hpoint (Ioo_subset_Icc_self hr) ht))
  have hKU : cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ ρ ⊆ cylinderDomain ρ := by
    intro x hx
    exact cylinderShell_subset_domain hρ ⟨hx.1,hx.2.1,by linarith [hx.2.2]⟩
  have ht := cylinderTimeTrace_le_average_on (cylinderDomain_isOpen ρ) hf hρ.le hKU
    (fun x hx => hn x (hKU hx))
  have hdiff : 0 < Real.log 3-Real.log ρ :=
    sub_pos.mpr (Real.log_lt_log hρ (by linarith))
  have hr' : cylinderAverage f ρ*Real.log 3 ≤
      (D*f (cylinderPoint 0 1 θ))*(4*(Real.log 3-Real.log ρ)) := by
    apply (div_le_iff₀ (show 0 < 4*(Real.log 3-Real.log ρ) by positivity)).mp
    simpa only [mul_div_assoc] using hr.trans ho
  have hinner : cylinderAverage f ρ ≤
      (4*D/Real.log 3)*(Real.log 3-Real.log ρ)*f (cylinderPoint 0 1 θ) := by
    calc
      _ ≤ ((D*f (cylinderPoint 0 1 θ))*(4*(Real.log 3-Real.log ρ)))/Real.log 3 :=
        (le_div_iff₀ hl3).mpr hr'
      _ = _ := by ring
  have hlog : Real.log 3-Real.log ρ ≤ (Real.log 3+1)*(1+|Real.log ρ|) := by
    nlinarith [neg_le_abs (Real.log ρ), abs_nonneg (Real.log ρ)]
  have hfinal := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (show 0 ≤ 8*D/Real.log 3 by positivity) hsrc)
  calc
    _ ≤ 2*cylinderAverage f ρ := ht
    _ ≤ 2*((4*D/Real.log 3)*(Real.log 3-Real.log ρ)*f (cylinderPoint 0 1 θ)) :=
      mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ ≤ C*(1+|Real.log ρ|)*f (cylinderPoint 0 1 θ) := by
      dsimp [C]
      convert hfinal using 1 <;> ring

end KakeyaSharp.Propagation
