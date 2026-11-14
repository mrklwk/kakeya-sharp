/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Trace.Sublevel
public import KakeyaSharp.Trace.LayerCake
public import KakeyaSharp.ThinMaximum

@[expose] public section

/-! The weighted trace bound from comparison and layer cake. The constant is
dimension dependent; the power of the barrier height is exactly m. The
barrier has no prescribed boundary values. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp
open Set MeasureTheory Filter KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff ENNReal Topology

def thinTraceConstant (m : ℕ) : ℝ := 3^(m+1)*((m : ℝ)+1)

theorem thinTraceConstant_pos (m : ℕ) : 0 < thinTraceConstant m := by
  unfold thinTraceConstant
  positivity

theorem thinTrace_bound_global {m : ℕ} {R H : ℝ} (hR : 0 < R) (hH : 0 < H)
    (o : ThinSpace m) {u φ : ThinSpace m → ℝ}
    (hu : ContDiff ℝ 3 u) (hφ : ContDiff ℝ 3 φ)
    (hzu : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2=R^2 → u z=0)
    (hu0 : ∀ z ∈ thinBallAt R o, u z ≤ 0)
    (hbound : ∀ z ∈ thinClosedBallAt R o, -H ≤ φ z ∧ φ z ≤ 0)
    (hpu : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian u z) a)
    (hpφ : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian φ z) a) :
    (∫ z in thinBallAt R o, (-u z)^(m+1)*mooreDet m (thinQuaternionHessian φ z)) ≤
      thinTraceConstant m*H^m*determinantEnergyAt R o u := by
  classical
  let μ : Measure (ThinSpace m) := volume.restrict (thinBallAt R o)
  let du : ThinSpace m → ℝ := fun z => mooreDet m (thinQuaternionHessian u z)
  let dφ : ThinSpace m → ℝ := fun z => mooreDet m (thinQuaternionHessian φ z)
  have hdu : Continuous du := (continuous_mooreDet m).comp (thinHessian_continuous hu)
  have hdφ : Continuous dφ := (continuous_mooreDet m).comp (thinHessian_continuous hφ)
  have hdu0 : 0 ≤ᵐ[μ] du := by
    filter_upwards [ae_restrict_mem (thinBallAt_measurable R o)] with z hz
    exact thinDet_nonneg (hu.contDiffAt.of_le (by norm_num)) (hpu z hz)
  have hdφ0 : 0 ≤ᵐ[μ] dφ := by
    filter_upwards [ae_restrict_mem (thinBallAt_measurable R o)] with z hz
    exact thinDet_nonneg (hφ.contDiffAt.of_le (by norm_num)) (hpφ z hz)
  have hU0 : 0 ≤ᵐ[μ] (fun z => -u z) := by
    filter_upwards [ae_restrict_mem (thinBallAt_measurable R o)] with z hz
    exact neg_nonneg.mpr (hu0 z hz)
  have hdui : Integrable du μ := continuous_integrableOn_thinBallAt hR o hdu
  have hdφi : Integrable dφ μ := continuous_integrableOn_thinBallAt hR o hdφ
  have htail (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (t^m)*(μ.withDensity (fun z => ENNReal.ofReal (dφ z))) {z | 3*t < -u z} ≤
      ENNReal.ofReal (H^m)*(μ.withDensity (fun z => ENNReal.ofReal (du z))) {z | t < -u z} := by
    rw [withDensity_ofReal_apply_eq_integral_indicator (s := {z | 3*t < -u z}) hdφi hdφ0
        (isOpen_lt continuous_const hu.continuous.neg).measurableSet,
      withDensity_ofReal_apply_eq_integral_indicator (s := {z | t < -u z}) hdui hdu0
        (isOpen_lt continuous_const hu.continuous.neg).measurableSet,
      ← ENNReal.ofReal_mul (pow_nonneg ht.le m), ← ENNReal.ofReal_mul (pow_nonneg hH.le m)]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left (thinDet_sublevel_bound hR hH ht o hu hφ hzu hbound hpu hpφ)
      (pow_nonneg hH.le m)
    have hc : H^m*(t/H)^m=t^m := by rw [← mul_pow]; congr 1; field_simp
    rw [← mul_assoc, hc] at h
    exact h
  have hmoment := lintegral_moment_le_of_scaled_tails
    (μ.withDensity (fun z => ENNReal.ofReal (du z)))
    (μ.withDensity (fun z => ENNReal.ofReal (dφ z))) m hH.le
    ((withDensity_absolutelyContinuous μ _).ae_le hU0)
    ((withDensity_absolutelyContinuous μ _).ae_le hU0) hu.continuous.neg.measurable htail
  have hip : Integrable (fun z => (-u z)^(m+1)*dφ z) μ :=
    continuous_integrableOn_thinBallAt hR o ((hu.continuous.neg.pow _).mul hdφ)
  have hie : Integrable (fun z => (-u z)*du z) μ :=
    continuous_integrableOn_thinBallAt hR o (hu.continuous.neg.mul hdu)
  rw [lintegral_withDensity_ofReal_eq_integral (f := fun z => (-u z)^(m+1)) hdφ.measurable
      (hu.continuous.neg.pow _).measurable hdφ0 (hU0.mono (fun z hz => pow_nonneg hz _)) hip,
    lintegral_withDensity_ofReal_eq_integral (f := fun z => -u z) hdu.measurable hu.continuous.neg.measurable hdu0 hU0 hie,
    ← ENNReal.ofReal_mul (by positivity)] at hmoment
  apply (ENNReal.ofReal_le_ofReal_iff _).mp hmoment
  exact mul_nonneg (mul_nonneg (thinTraceConstant_pos m).le (pow_nonneg hH.le m))
    (integral_nonneg_of_ae (by filter_upwards [hU0,hdu0] with z hz hz'; exact mul_nonneg hz hz'))

theorem ThinAdmissibleAt.trace_bound_of_pos {m : ℕ} (hm : 1 ≤ m) {R H : ℝ}
    (hR : 0 < R) (hH : 0 < H) {o : ThinSpace m} {u φ : ThinSpace m → ℝ}
    (hu : ThinAdmissibleAt R o u)
    (hφ : ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 3 φ z)
    (hbound : ∀ z ∈ thinClosedBallAt R o, -H ≤ φ z ∧ φ z ≤ 0)
    (hpφ : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian φ z) a) :
    (∫ z in thinBallAt R o, (-u z)^(m+1)*mooreDet m (thinQuaternionHessian φ z)) ≤
      thinTraceConstant m*H^m*determinantEnergyAt R o u := by
  obtain ⟨u',hu',hzu',hpu',heu⟩ := hu.exists_C3_representative hR
  obtain ⟨φ',hφ',heφ⟩ := exists_global_C3_extension (thinClosedBallAt_compact hR.le o) hφ
  have hc (z : ThinSpace m) (hz : z ∈ thinBallAt R o) : z ∈ thinClosedBallAt R o :=
    show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le
  have hb' : ∀ z ∈ thinClosedBallAt R o, -H ≤ φ' z ∧ φ' z ≤ 0 := by
    intro z hz
    rw [(heφ z hz).self_of_nhds]
    exact hbound z hz
  have hp' : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian φ' z) a := by
    intro z hz a
    rw [thinQuaternionHessian_congr_nhds (heφ z (hc z hz))]
    exact hpφ z hz a
  have hu0' : ∀ z ∈ thinBallAt R o, u' z ≤ 0 := by
    intro z hz
    rw [(heu z (hc z hz)).self_of_nhds]
    exact hu.nonpos hm hR z (hc z hz)
  have h := thinTrace_bound_global hR hH o hu' hφ' hzu' hu0' hb' hpu' hp'
  have hi : (∫ z in thinBallAt R o, (-u' z)^(m+1)*mooreDet m (thinQuaternionHessian φ' z)) =
      ∫ z in thinBallAt R o, (-u z)^(m+1)*mooreDet m (thinQuaternionHessian φ z) := by
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only
    rw [(heu z (hc z hz)).self_of_nhds, thinQuaternionHessian_congr_nhds (heφ z (hc z hz))]
  have he : determinantEnergyAt R o u' = determinantEnergyAt R o u := by
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only
    rw [(heu z (hc z hz)).self_of_nhds, thinQuaternionHessian_congr_nhds (heu z (hc z hz))]
  rwa [hi,he] at h

theorem ThinAdmissibleAt.trace_bound {m : ℕ} (hm : 1 ≤ m) {R H : ℝ}
    (hR : 0 < R) (hH : 0 ≤ H) {o : ThinSpace m} {u φ : ThinSpace m → ℝ}
    (hu : ThinAdmissibleAt R o u)
    (hφ : ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 3 φ z)
    (hbound : ∀ z ∈ thinClosedBallAt R o, -H ≤ φ z ∧ φ z ≤ 0)
    (hpφ : ∀ z ∈ thinBallAt R o, ∀ a, 0 ≤ quaternionForm (thinQuaternionHessian φ z) a) :
    (∫ z in thinBallAt R o, (-u z)^(m+1)*mooreDet m (thinQuaternionHessian φ z)) ≤
      thinTraceConstant m*H^m*determinantEnergyAt R o u := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ z in thinBallAt R o, (-u z)^(m+1)*mooreDet m (thinQuaternionHessian φ z)) ≤
        thinTraceConstant m*(H+ε)^m*determinantEnergyAt R o u := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hu.trace_bound_of_pos hm hR (add_pos_of_nonneg_of_pos hH hε) hφ
      (fun z hz => ⟨by have hh := (hbound z hz).1; change 0 < ε at hε; linarith,
        (hbound z hz).2⟩) hpφ
  have ht : Tendsto (fun ε : ℝ => thinTraceConstant m*(H+ε)^m*determinantEnergyAt R o u)
      (𝓝[>] 0) (𝓝 (thinTraceConstant m*H^m*determinantEnergyAt R o u)) := by
    have hcont : Continuous (fun ε : ℝ => thinTraceConstant m*(H+ε)^m*determinantEnergyAt R o u) := by
      fun_prop
    simpa only [add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht he

end KakeyaSharp
