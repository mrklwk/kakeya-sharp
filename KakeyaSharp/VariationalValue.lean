/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.AdmissibleIntegrability

@[expose] public section

/-! The thin-source estimate for the supremum over actual admissible functions.
The supremum is extended-real-valued: its finiteness is not assumed or proved here. -/

noncomputable section
open MeasureTheory Set Metric
namespace KakeyaSharp

def thinVariationalValueAt {m : ℕ} (R : ℝ) (o : ThinSpace m) (μ : ThinSpace m → ℝ) : EReal :=
  ⨆ f : {f : ThinSpace m → ℝ // ThinAdmissibleAt R o f}, (thinFunctionalAt R o μ f : EReal)

theorem thinSource_value_lower_scaled {m : ℕ} (hm : 1 ≤ m) {R ε a : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (hεR : ε ≤ R / 10) (ha : 0 ≤ a)
    (o : ThinSpace m) {μ : ThinSpace m → ℝ}
    (hμ : ContinuousOn μ (thinClosedBallAt R o))
    (hμ0 : ∀ z ∈ thinBallAt R o, 0 ≤ μ z)
    (hμa : ∀ z ∈ thinCoreAt R ε o, a ≤ μ z) :
    ((thinLowerConstant m * R ^ m * ε ^ (2 * m + 2) *
      a ^ (((m : ℝ) + 1) / m) * Real.log (R / ε) : ℝ) : EReal) ≤
        thinVariationalValueAt R o μ := by
  obtain ⟨v, hv, hval⟩ := thinSource_variational_lower_scaled hm hR hε hεR ha o hμ hμ0 hμa
  exact (EReal.coe_le_coe_iff.mpr hval).trans (le_iSup
    (fun f : {f : ThinSpace m → ℝ // ThinAdmissibleAt R o f} =>
      (thinFunctionalAt R o μ f : EReal)) ⟨v, hv⟩)

end KakeyaSharp
