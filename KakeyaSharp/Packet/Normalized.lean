/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Mass
public import KakeyaSharp.Packet.ScalarTransfer

@[expose] public section

/-! Mass-one packets and finite weighted families with the scalar-transfer theorem. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace KakeyaSharp.Packet
open MeasureTheory Set Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Green
open scoped ContDiff

def packetMass (m : ℕ) (r h : ℝ) (χ : ℝ → ℝ) : ℝ :=
  ((Real.sqrt h)^3/Real.sqrt r)^m * cutoffMass m χ

theorem packetMass_pos {m : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hχpos : ∀ t, 0 ≤ χ t) (hχzero : 0 < χ 0)
    {M : ℝ} (hχsupp : ∀ t, M < t → χ t=0) : 0 < packetMass m r h χ := by
  have hc := cutoffMass_pos (m := m) hχ hχpos hχzero hχsupp
  unfold packetMass
  positivity

theorem packetMass_kakeya_scale (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (χ : ℝ → ℝ) :
    packetMass m (δ^2) (δ^4) χ = δ^(5*m)*cutoffMass m χ := by
  have hs : Real.sqrt (δ^4) = δ^2 := by
    rw [show δ^4 = (δ^2)^2 by ring, Real.sqrt_sq (sq_nonneg δ)]
  unfold packetMass
  rw [hs, Real.sqrt_sq hδ.le]
  have he : (δ^2)^3/δ = δ^5 := by field_simp
  rw [he, ← pow_mul]

def normalizedPacket {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (χ : ℝ → ℝ)
    (y : ThinCurrentSpace m) : Matrix (Fin (m+1)) (Fin (m+1)) Q :=
  (packetMass m r h χ)⁻¹ • rawPacket r h a v χ y

theorem normalizedPacket_density {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (χ : ℝ → ℝ)
    (y : ThinCurrentSpace m) :
    currentDensity (normalizedPacket r h a v χ) y = (packetMass m r h χ)⁻¹*packetWeight r h a v χ y := by
  change ((packetMass m r h χ)⁻¹ • rawPacket r h a v χ y 0 0).re = _
  rw [Quaternion.re_smul, smul_eq_mul]
  congr 1
  exact rawPacket_density r h a v χ y

theorem integral_normalizedPacket_density {m : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (a v : Fin m → ℝ) {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m)))
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hχpos : ∀ t, 0 ≤ χ t) (hχzero : 0 < χ 0)
    {M : ℝ} (hχsupp : ∀ t, M < t → χ t=0) :
    (∫ z : ThinSpace m, currentDensity (normalizedPacket r h a v χ) (p,z)) = 1 := by
  simp only [normalizedPacket_density]
  rw [integral_const_mul, integral_packetWeight hr hh a v hp hχ]
  exact inv_mul_cancel₀ (packetMass_pos hr hh hχ hχpos hχzero hχsupp).ne'

def normalizedPacketFamily {m N : ℕ} (r h : ℝ) (a v : Fin N → Fin m → ℝ)
    (weights : Fin N → ℝ) (χ : ℝ → ℝ) :
    ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) Q :=
  packetFamily r h a v (fun l => weights l / packetMass m r h χ) χ

theorem normalizedPacketFamily_density_integrable {m N : ℕ} {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m)))
    {χ : ℝ → ℝ} (hχ : Continuous χ) {M : ℝ} (hχsupp : ∀ t, M < t → χ t=0) :
    Integrable (fun z : ThinSpace m => currentDensity (normalizedPacketFamily r h a v weights χ) (p,z)) := by
  simp only [normalizedPacketFamily, packetFamily_density, familyWeights]
  apply integrable_finsetSum
  intro l _
  exact (packetWeight_integrable hr hh (a l) (v l) hp hχ hχsupp).const_mul _

theorem integral_normalizedPacketFamily_density {m N : ℕ} {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m)))
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hχpos : ∀ t, 0 ≤ χ t) (hχzero : 0 < χ 0)
    {M : ℝ} (hχsupp : ∀ t, M < t → χ t=0) :
    (∫ z : ThinSpace m, currentDensity (normalizedPacketFamily r h a v weights χ) (p,z)) =
      ∑ l, weights l := by
  simp only [normalizedPacketFamily, packetFamily_density, familyWeights]
  rw [integral_finsetSum _ (fun l _ =>
    (packetWeight_integrable hr hh (a l) (v l) hp hχ hχsupp).const_mul _)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul, integral_packetWeight hr hh (a l) (v l) hp hχ]
  exact div_mul_cancel₀ _ (packetMass_pos hr hh hχ hχpos hχzero hχsupp).ne'

theorem normalizedPacketFamily_weakSuperharmonic
    {m N : ℕ} (hm : 1 ≤ m) {r h R M : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hR : 0 < R)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχpos : ∀ t, 0 ≤ χ t) (hχzero : 0 < χ 0)
    (hχsupp : ∀ t, M < t → χ t=0)
    (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    (hY : ∀ p ∈ Ω, 0 < radius (p,(0 : ThinSpace m)))
    (hbound : ∀ p ∈ Ω, ∀ l, supportBound r (h*M) (a l) (v l) p < R^2) :
    WeakSuperharmonicOn Ω (fun p => thinValueRealAt R 0
      (thinSlice (currentDensity (normalizedPacketFamily r h a v weights χ)) p)) := by
  exact packetFamily_weakSuperharmonic hm hr hh hR a v
    (fun l => div_nonneg (hw l) (packetMass_pos hr hh hχ.continuous hχpos hχzero hχsupp).le)
    hχ hχpos hχsupp Ω hΩ hY hbound

/-- A fixed smooth cutoff, equal to one for t ≤ 1/2 and zero for t ≥ 1. -/
def standardCutoff (t : ℝ) : ℝ := Real.smoothTransition (2-2*t)

theorem standardCutoff_smooth : ContDiff ℝ ∞ standardCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))

theorem standardCutoff_nonneg (t : ℝ) : 0 ≤ standardCutoff t := Real.smoothTransition.nonneg _

theorem standardCutoff_eq_one {t : ℝ} (ht : t ≤ 1/2) : standardCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem standardCutoff_eq_zero {t : ℝ} (ht : 1 ≤ t) : standardCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem standardCutoff_zero : standardCutoff 0 = 1 := standardCutoff_eq_one (by norm_num)

theorem standardCutoff_mass_pos (m : ℕ) : 0 < cutoffMass m standardCutoff :=
  cutoffMass_pos standardCutoff_smooth.continuous standardCutoff_nonneg
    (by rw [standardCutoff_zero]; norm_num)
    (fun _ ht => standardCutoff_eq_zero ht.le)

def unitPacketFamily {m N : ℕ} (r h : ℝ) (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ) :=
  normalizedPacketFamily r h a v weights standardCutoff

theorem unitPacketFamily_mass {m N : ℕ} {r h : ℝ} (hr : 0 < r) (hh : 0 < h)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    {p : Space 3} (hp : 0 < radius (p,(0 : ThinSpace m))) :
    (∫ z : ThinSpace m, currentDensity (unitPacketFamily r h a v weights) (p,z)) = ∑ l, weights l :=
  integral_normalizedPacketFamily_density hr hh a v weights hp
    standardCutoff_smooth.continuous standardCutoff_nonneg
    (by rw [standardCutoff_zero]; norm_num) (fun _ ht => standardCutoff_eq_zero ht.le)

theorem unitPacketFamily_weakSuperharmonic
    {m N : ℕ} (hm : 1 ≤ m) {r h R : ℝ} (hr : 0 < r) (hh : 0 < h) (hR : 0 < R)
    (a v : Fin N → Fin m → ℝ) {weights : Fin N → ℝ} (hw : ∀ l, 0 ≤ weights l)
    (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    (hY : ∀ p ∈ Ω, 0 < radius (p,(0 : ThinSpace m)))
    (hbound : ∀ p ∈ Ω, ∀ l, supportBound r h (a l) (v l) p < R^2) :
    WeakSuperharmonicOn Ω (fun p => thinValueRealAt R 0
      (thinSlice (currentDensity (unitPacketFamily r h a v weights)) p)) := by
  apply normalizedPacketFamily_weakSuperharmonic hm hr hh hR a v hw
    standardCutoff_smooth standardCutoff_nonneg
    (by rw [standardCutoff_zero]; norm_num) (M := 1)
    (fun _ ht => standardCutoff_eq_zero ht.le) Ω hΩ hY
  simpa only [mul_one] using hbound

end KakeyaSharp.Packet
