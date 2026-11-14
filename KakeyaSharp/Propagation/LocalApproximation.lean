/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Propagation.Mollifier
public import KakeyaSharp.LocalExtension

@[expose] public section

/-! Smooth nonnegative superharmonic approximations on a compact interior set.
The construction uses a continuous extension only outside that set. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Propagation
open MeasureTheory Set Metric Filter Laplacian OAI.Analysis.PDE.Schauder
open scoped ContDiff Topology

theorem exists_local_superharmonic_approximation
    {Ω K : Set (Space 3)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {f : Space 3 → ℝ} (hf : ContinuousOn f Ω) (hw : Green.WeakSuperharmonicOn Ω f)
    (hn : ∀ x ∈ Ω, 0 ≤ f x) :
    ∃ F : ℕ → Space 3 → ℝ, ∃ M : ℝ, 0 ≤ M ∧
      (∀ n, ContDiff ℝ ∞ (F n)) ∧
      (∀ n x, x ∈ K → 0 ≤ F n x ∧ Δ (F n) x ≤ 0 ∧ ‖F n x‖ ≤ M) ∧
      (∀ x ∈ K, Tendsto (fun n => F n x) atTop (𝓝 (f x))) := by
  obtain ⟨g,hg,he⟩ := exists_global_contDiff_extension 0 hK (fun x hx =>
    contDiffAt_zero.mpr ⟨Ω,hΩ.mem_nhds (hKΩ hx),hf⟩)
  have hgc : Continuous g := hg.continuous
  let V := Ω ∩ interior {x | g x=f x}
  have hV : IsOpen V := hΩ.inter isOpen_interior
  have hKV : K ⊆ V := by
    intro x hx
    exact ⟨hKΩ hx,mem_interior_iff_mem_nhds.mpr (he x hx)⟩
  obtain ⟨ε,hε,hεV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨M,hM⟩ := hK.cthickening.exists_bound_of_continuousOn
    (s := cthickening ε K) hgc.continuousOn
  have hr := (standardMollifier_radius_tendsto 3).eventually (gt_mem_nhds hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hr
  let F : ℕ → Space 3 → ℝ := fun n => mollified (standardMollifier 3 (n+N)) g
  have hradius (n : ℕ) : (standardMollifier 3 (n+N)).rOut ≤ ε := (hN _ (by omega)).le
  have hball (n : ℕ) {x : Space 3} (hx : x ∈ K) :
      closedBall x (standardMollifier 3 (n+N)).rOut ⊆ cthickening ε K :=
    (closedBall_subset_closedBall (hradius n)).trans (closedBall_subset_cthickening hx ε)
  have hEq (y : Space 3) (hy : y ∈ cthickening ε K) : g y=f y :=
    show y ∈ {x | g x=f x} from interior_subset (hεV hy).2
  refine ⟨F,max M 0,le_max_right _ _,fun n => mollified_smooth _ hgc,?_,?_⟩
  · intro n x hx
    refine ⟨mollified_nonneg _ x (fun y hy => by
      rw [hEq y (hball n hx hy)]
      exact hn y (hεV (hball n hx hy)).1),?_,?_⟩
    · exact mollified_laplacian_nonpos _ hgc hw x
        (fun y hy => (hεV (hball n hx hy)).1)
        (fun y hy => hEq y (hball n hx hy))
    · exact (mollified_norm_le _ x (fun y hy => hM y (hball n hx hy))).trans (le_max_left _ _)
  · intro x hx
    rw [← (he x hx).self_of_nhds]
    exact (mollified_tendsto hgc x).comp (tendsto_add_atTop_nat N)

end KakeyaSharp.Propagation
