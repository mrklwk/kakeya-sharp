/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.WeakSuperharmonicLimit
public import KakeyaSharp.VariationalContinuity
public import KakeyaSharp.ThinParameterHessian

@[expose] public section

/-! Passing the actual variational value through scalar source regularization.
No positive lower bound for the limiting source is needed. -/
noncomputable section
namespace KakeyaSharp
open Set Filter KakeyaSharp.Green
open scoped Topology

theorem thinValueRealAt_weakSuperharmonic_regularization {m : ℕ} (hm : 1 ≤ m)
    {R : ℝ} (hR : 0 < R) (o : ThinSpace m) (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    {ρ : ThinCurrentSpace m → ℝ} (hρ : Continuous ρ)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hεb : ∀ n, ε n ∈ Icc (0 : ℝ) 1)
    (hweak : ∀ n, WeakSuperharmonicOn Ω (fun p => thinValueRealAt R o (fun z => ρ (p,z)+ε n))) :
    WeakSuperharmonicOn Ω (fun p => thinValueRealAt R o (thinSlice ρ p)) := by
  apply weakSuperharmonicOn_of_tendsto hΩ hweak
  · intro p
    exact thinValueRealAt_regularization hm hR o
      (hρ.comp (continuous_const.prodMk continuous_id)).continuousOn hε
      (Eventually.of_forall (fun n => (hεb n).1))
  · intro K hK _
    obtain ⟨C,hC⟩ := (hK.prod (thinClosedBallAt_compact hR.le o)).exists_bound_of_continuousOn hρ.continuousOn
    let A : ℝ := max C 0 + 1
    let M : ℝ := thinValueRealAt R o (fun _ => A)
    refine ⟨M, thinValueRealAt_nonneg hm hR o continuousOn_const, ?_⟩
    intro n p hp
    have hc : ContinuousOn (fun z => ρ (p,z)+ε n) (thinClosedBallAt R o) :=
      ((hρ.comp (continuous_const.prodMk continuous_id)).add continuous_const).continuousOn
    rw [abs_of_nonneg (thinValueRealAt_nonneg hm hR o hc)]
    apply thinValueRealAt_mono hm hR o hc continuousOn_const
    intro z hz
    have hb := hC (p,z) ⟨hp,show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le⟩
    have hh : ρ (p,z) ≤ C := (le_abs_self _).trans hb
    dsimp only [A]
    linarith [le_max_left C 0, (hεb n).2]

end KakeyaSharp
