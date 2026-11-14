/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ScaledVariational

@[expose] public section

/-! Every admissible test has genuine integrable energy and source terms. -/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff
namespace KakeyaSharp
open KakeyaSharp.Moore

theorem thinClosedBallAt_compact {m : ℕ} {R : ℝ} (hR : 0 ≤ R) (o : ThinSpace m) :
    IsCompact (thinClosedBallAt R o) := by
  have hc : IsClosed (thinClosedBallAt R o) := isClosed_le (by fun_prop) continuous_const
  apply (isCompact_closedBall o R).of_isClosed_subset hc
  intro z hz
  change ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 ≤ R ^ 2 at hz
  have hx : ‖z.1 - o.1‖ ≤ R := by
    nlinarith [sq_nonneg ‖z.2 - o.2‖, norm_nonneg (z.1 - o.1)]
  have hp : ‖z.2 - o.2‖ ≤ R := by
    nlinarith [sq_nonneg ‖z.1 - o.1‖, norm_nonneg (z.2 - o.2)]
  simpa [mem_closedBall, dist_eq_norm, Prod.norm_def] using max_le hx hp

theorem ThinAdmissibleAt.energy_integrableOn {m : ℕ} {R : ℝ} (hR : 0 < R)
    {o : ThinSpace m} {f : ThinSpace m → ℝ} (hf : ThinAdmissibleAt R o f) :
    IntegrableOn (fun z => (-f z) * mooreDet m (thinQuaternionHessian f z)) (thinBallAt R o) := by
  have hc : ContinuousOn (fun z => (-f z) * mooreDet m (thinQuaternionHessian f z))
      (thinClosedBallAt R o) := by
    intro z hz
    have hs := hf.1 z hz
    have hh := thinQuaternionHessian_continuousAt hs
    exact (hs.continuousAt.neg.mul ((continuous_mooreDet m).continuousAt.comp hh)).continuousWithinAt
  exact (hc.integrableOn_compact (thinClosedBallAt_compact hR.le o)).mono_set
    (fun z hz => show ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 ≤ R ^ 2 from hz.le)

theorem ThinAdmissibleAt.source_integrableOn {m : ℕ} {R : ℝ} (hR : 0 < R)
    {o : ThinSpace m} {f μ : ThinSpace m → ℝ} (hf : ThinAdmissibleAt R o f)
    (hμ : ContinuousOn μ (thinClosedBallAt R o)) :
    IntegrableOn (fun z => (-f z) * μ z) (thinBallAt R o) := by
  have hc : ContinuousOn f (thinClosedBallAt R o) :=
    fun z hz => (hf.1 z hz).continuousAt.continuousWithinAt
  exact ((hc.neg.mul hμ).integrableOn_compact (thinClosedBallAt_compact hR.le o)).mono_set
    (fun z hz => show ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 ≤ R ^ 2 from hz.le)

end KakeyaSharp
