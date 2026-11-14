/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Affine
public import KakeyaSharp.Packet.Smooth

@[expose] public section

/-! Exact packet mass and its independence of the parameter and packet center. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace KakeyaSharp.Packet
open Matrix MeasureTheory Set

theorem packetAffine_continuous {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (p : Space 3) :
    Continuous (packetAffine r h a v p) :=
  (unpack m).continuous.comp
    ((Matrix.toLin' (shapeMatrix m r h (radius (p,(0 : ThinSpace m)))
      (p 0-1) (p 1) (p 2))).continuous_of_finiteDimensional.add continuous_const)

theorem packetAffine_map_volume {m : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (a v : Fin m → ℝ) {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m))) :
    Measure.map (packetAffine r h a v p) volume =
      ENNReal.ofReal ((packetJacobian r h (radius (p,(0 : ThinSpace m))) (p 0-1)^m)⁻¹) • volume := by
  let A := shapeMatrix m r h (radius (p,(0 : ThinSpace m))) (p 0-1) (p 1) (p 2)
  have hd : A.det = packetJacobian r h (radius (p,(0 : ThinSpace m))) (p 0-1)^m :=
    det_shapeMatrix m hr hh hp (radius_sq (p,(0 : ThinSpace m))).symm
  have hpos : 0 < A.det := by rw [hd]; exact pow_pos (packetJacobian_pos hr hh hp _) m
  have hlin := (Matrix.toLin' A).continuous_of_finiteDimensional
  have hadd : Continuous (fun z : PacketCoordinates m => z+packetTranslation a v p) :=
    continuous_id.add continuous_const
  change Measure.map ((unpack m) ∘ (fun z => z+packetTranslation a v p) ∘ Matrix.toLin' A) volume = _
  rw [← Measure.map_map (unpack m).continuous.measurable (hadd.comp hlin).measurable,
    ← Measure.map_map hadd.measurable hlin.measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hpos.ne', Measure.map_smul,
    (measurePreserving_add_right volume (packetTranslation a v p)).map_eq,
    Measure.map_smul, (unpack_measurePreserving m).map_eq, abs_of_pos (inv_pos.mpr hpos), hd]
  · exact (unpack m).continuous.measurable.aemeasurable
  · exact hadd.measurable.aemeasurable

theorem integral_packetAffine {m : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (a v : Fin m → ℝ) {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m)))
    {f : ThinSpace m → ℝ} (hf : Continuous f) :
    (∫ z, f z) = packetJacobian r h (radius (p,(0 : ThinSpace m))) (p 0-1)^m *
      ∫ z : PacketCoordinates m, f (packetAffine r h a v p z) := by
  have hj := pow_pos (packetJacobian_pos hr hh hp (p 0-1)) m
  have he := integral_map (μ := volume) (packetAffine_continuous r h a v p).measurable.aemeasurable
    hf.aestronglyMeasurable
  rw [packetAffine_map_volume hr hh a v hp, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hj.le), smul_eq_mul] at he
  rw [← he, ← mul_assoc, mul_inv_cancel₀ hj.ne', one_mul]

theorem integrable_packetAffine_iff {m : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (a v : Fin m → ℝ) {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m)))
    {f : ThinSpace m → ℝ} (hf : Continuous f) :
    Integrable (fun z => f (packetAffine r h a v p z)) ↔ Integrable f := by
  have hj := pow_pos (packetJacobian_pos hr hh hp (p 0-1)) m
  have he := integrable_map_measure (μ := volume) hf.aestronglyMeasurable
    (packetAffine_continuous r h a v p).measurable.aemeasurable
  rw [packetAffine_map_volume hr hh a v hp,
    integrable_smul_measure (ENNReal.ofReal_pos.mpr (inv_pos.mpr hj)).ne' ENNReal.ofReal_ne_top] at he
  exact he.symm

theorem packetSquare_continuous (m : ℕ) : Continuous (@packetSquare m) := by
  unfold packetSquare
  fun_prop

theorem packetSquare_eq_norm_sq {m : ℕ} (z : PacketCoordinates m) :
    packetSquare z = ‖WithLp.toLp 2 z‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem cutoff_packetSquare_compact {m : ℕ} {χ : ℝ → ℝ} {M : ℝ}
    (hχsupp : ∀ t, M < t → χ t=0) : HasCompactSupport (fun z : PacketCoordinates m => χ (packetSquare z)) := by
  have he : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3 × Fin m) => χ (‖z‖^2)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3 × Fin m))
      (Real.sqrt (max M 0)))
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    apply hχsupp
    have hsq := Real.sq_sqrt (le_max_right M 0)
    have hnorm := norm_nonneg z
    have hsqrt := Real.sqrt_nonneg (max M 0)
    have hM := le_max_left M 0
    nlinarith
  have hc := he.comp_homeomorph (PiLp.homeomorph 2 (fun _ : Fin 3 × Fin m => ℝ)).symm
  convert hc using 1
  funext z
  exact congrArg χ (packetSquare_eq_norm_sq z)

theorem cutoff_packetSquare_integrable {m : ℕ} {χ : ℝ → ℝ} (hχ : Continuous χ) {M : ℝ}
    (hχsupp : ∀ t, M < t → χ t=0) : Integrable (fun z : PacketCoordinates m => χ (packetSquare z)) :=
  (hχ.comp (packetSquare_continuous m)).integrable_of_hasCompactSupport
    (cutoff_packetSquare_compact hχsupp)

def cutoffMass (m : ℕ) (χ : ℝ → ℝ) : ℝ := ∫ z : PacketCoordinates m, χ (packetSquare z)

theorem cutoffMass_pos {m : ℕ} {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hχpos : ∀ t, 0 ≤ χ t) (hχzero : 0 < χ 0) {M : ℝ}
    (hχsupp : ∀ t, M < t → χ t=0) : 0 < cutoffMass m χ := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (hχ.comp (packetSquare_continuous m)) (cutoff_packetSquare_integrable hχ hχsupp)
    (fun z => hχpos _) (x := 0)
  simpa [packetSquare] using hχzero.ne'

theorem physicalCutoff_continuous {m : ℕ} {r : ℝ} (hr : 0 < r) (h : ℝ)
    (a v : Fin m → ℝ) {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m)))
    {χ : ℝ → ℝ} (hχ : Continuous χ) :
    Continuous (fun z : ThinSpace m => χ (physicalPhase r a v (p,z)/h)) := by
  apply hχ.comp
  apply Continuous.div_const
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (physicalPhase_contDiffAt (n := 1) hr a v (y := (p,z)) hp).continuousAt.comp
    (continuous_const.prodMk continuous_id).continuousAt

theorem integral_packetWeight {m : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (a v : Fin m → ℝ) {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m)))
    {χ : ℝ → ℝ} (hχ : Continuous χ) :
    (∫ z : ThinSpace m, packetWeight r h a v χ (p,z)) =
      ((Real.sqrt h)^3/Real.sqrt r)^m * cutoffMass m χ := by
  change (∫ z : ThinSpace m, prefactor m r (radius (p,(0 : ThinSpace m))) (p 0-1)*
    χ (physicalPhase r a v (p,z)/h)) = _
  rw [integral_const_mul, integral_packetAffine hr hh a v hp (physicalCutoff_continuous hr h a v hp hχ)]
  simp only [physicalPhase_packetAffine hr hh a v hp, mul_div_cancel_left₀ _ hh.ne']
  rw [← mul_assoc, prefactor_jacobian m hr hh hp]
  rfl

theorem packetWeight_integrable {m : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (a v : Fin m → ℝ) {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m)))
    {χ : ℝ → ℝ} (hχ : Continuous χ) {M : ℝ} (hχsupp : ∀ t, M < t → χ t=0) :
    Integrable (fun z : ThinSpace m => packetWeight r h a v χ (p,z)) := by
  have hi := (integrable_packetAffine_iff hr hh a v hp (physicalCutoff_continuous hr h a v hp hχ)).mp
    (by simpa only [physicalPhase_packetAffine hr hh a v hp, mul_div_cancel_left₀ _ hh.ne'] using
      cutoff_packetSquare_integrable (m := m) hχ hχsupp)
  exact hi.const_mul (prefactor m r (radius (p,(0 : ThinSpace m))) (p 0-1))

end KakeyaSharp.Packet
