/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.DirectionIntegral

@[expose] public section

/-! The sharp-logarithm transfer. The only analytic assumption of the main
theorem will be `SharpTubeBound n`; it is a parameter, not an axiom. -/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace KakeyaSharp

lemma critical_holder {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ).HolderConjugate (overlapExponent n) := by
  exact Real.HolderConjugate.conjExponent
    (by exact_mod_cast (show 1 < n by omega) : (1 : ℝ) < n)

lemma inverse_overlapExponent {n : ℕ} (_hn : 2 ≤ n) :
    1 / overlapExponent n = ((n : ℝ) - 1) / n := by
  simp [overlapExponent]

lemma log_scale_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < Real.log (2 / δ) := by
  apply Real.log_pos
  apply (lt_div_iff₀ hδ).mpr
  linarith

lemma logLoss_pos (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < logLoss n δ :=
  Real.rpow_pos_of_pos (log_scale_pos hδ hδ1) _

lemma memLp_weighted_tubes {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n)
    (a : Fin m → ℝ) (q : ℝ) :
    MemLp (fun y ↦ ∑ i, (tube δ (v i) (x i)).indicator (fun _ ↦ a i) y)
      (ENNReal.ofReal q) volume := by
  apply memLp_finsetSum
  intro i _
  exact memLp_indicator_const _ (measurableSet_tube _ _ _) _
    (.inr (volume_tube_lt_top _ _ _).ne)

/-- A scale-dependent overlap norm bound, with all constants quantified. -/
def TubeNormBound (n : ℕ) (loss : ℝ → ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∀ v x : Fin m → Space n, (∀ i, ‖v i‖ = 1) →
    (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
    ∀ a : Fin m → ℝ, (∀ i, 0 ≤ a i) →
      (∫ y, (∑ i, (tube (2 * δ) (v i) (x i)).indicator (fun _ ↦ a i) y) ^
        overlapExponent n) ^ (1 / overlapExponent n) ≤
      (A * loss δ * δ ^ ((n - 1 : ℕ) / overlapExponent n)) *
        (∑ i, a i ^ overlapExponent n) ^ (1 / overlapExponent n)

theorem sharpTube_to_norm {n : ℕ} (hn : 2 ≤ n) (hTube : SharpTubeBound n) :
    TubeNormBound n (logLoss n) := by
  obtain ⟨C, hC, hTube⟩ := hTube
  let q := overlapExponent n
  have hq : 0 < q := (critical_holder hn).symm.pos
  refine ⟨C ^ (1 / q), by positivity, ?_⟩
  intro m δ hδ hδ1 v x hv hsep a ha
  have hM (y : Space n) :
      0 ≤ ∑ i, (tube (2 * δ) (v i) (x i)).indicator (fun _ ↦ a i) y :=
    Finset.sum_nonneg fun i _ ↦ Set.indicator_nonneg (fun _ _ ↦ ha i) y
  have hI : 0 ≤ ∫ y, (∑ i,
      (tube (2 * δ) (v i) (x i)).indicator (fun _ ↦ a i) y) ^ q :=
    integral_nonneg fun y ↦ Real.rpow_nonneg (hM y) q
  have hsum : 0 ≤ ∑ i, a i ^ q :=
    Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (ha i) q
  have hL := (log_scale_pos hδ hδ1).le
  have h := Real.rpow_le_rpow hI (hTube m δ hδ hδ1 v x hv hsep a ha)
    (by positivity : 0 ≤ 1 / q)
  have hpow : (δ ^ (n - 1)) ^ (1 / q) = δ ^ ((n - 1 : ℕ) / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hlog : Real.log (2 / δ) ^ (1 / q) = logLoss n δ := by
    rw [show 1 / q = ((n : ℝ) - 1) / n from inverse_overlapExponent hn]
    rfl
  rw [Real.mul_rpow (by positivity) hsum,
    Real.mul_rpow (mul_nonneg hC.le hL) (by positivity),
    Real.mul_rpow hC.le hL, hpow, hlog] at h
  exact h

theorem tubeNorm_to_discrete {n : ℕ} (hn : 2 ≤ n) {loss : ℝ → ℝ}
    (hloss : ∀ δ, 0 < δ → δ ≤ 1 → 0 < loss δ)
    (hTube : TubeNormBound n loss) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ v : Fin m → Space n, (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      ∀ f : Space n → ℂ, MemLp f n volume →
        ∑ i, kakeyaMaximal (2 * δ) f (v i) ^ (n : ℝ) ≤
          ENNReal.ofReal (((A * loss δ * δ ^ ((n - 1 : ℕ) / overlapExponent n) *
            (∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ))) /
            (c * δ ^ (n - 1))) ^ (n : ℝ)) := by
  obtain ⟨A, hA, hTube⟩ := hTube
  obtain ⟨c, hc, hvolume⟩ := exists_volume_tube_real_lower (n := n) (by omega)
  refine ⟨A, c, hA, hc, ?_⟩
  intro m δ hδ hδ1 v hv hsep f hf
  have hL := (hloss δ hδ hδ1).le
  have hpq := critical_holder hn
  have hf' : MemLp f (ENNReal.ofReal (n : ℝ)) volume := by simpa using hf
  have hvol (i : Fin m) (x : Space n) :
      ENNReal.ofReal (c * δ ^ (n - 1)) ≤ volume (tube (2 * δ) (v i) x) := by
    calc
      _ ≤ ENNReal.ofReal (volume.real (tube δ (v i) x)) :=
        ENNReal.ofReal_le_ofReal (hvolume δ (v i) x hδ hδ1 (hv i))
      _ = volume (tube δ (v i) x) :=
        ENNReal.ofReal_toReal (volume_tube_lt_top δ (v i) x).ne
      _ ≤ _ := measure_mono (tube_mono (by linarith) _ _)
  apply finite_kakeya_moment_of_integral_bound hpq.lt.le
    (by positivity : 0 < c * δ ^ (n - 1)) (by positivity) v f hf' hvol
  intro x
  apply finite_set_integrals_of_overlap hpq (by positivity)
    (fun i ↦ tube (2 * δ) (v i) (x i))
    (fun i ↦ measurableSet_tube _ _ _) (fun i ↦ volume_tube_lt_top _ _ _) _ hf'
  intro a ha
  exact ⟨memLp_weighted_tubes _ v x a _, hTube m δ hδ hδ1 v x hv hsep a ha⟩

/-- Exact cancellation of the powers of the tube radius. -/
lemma critical_scale_identity {n : ℕ} (hn : 2 ≤ n)
    {A c L δ I : ℝ} (hA : 0 < A) (hc : 0 < c) (hL : 0 < L)
    (hδ : 0 < δ) (hI : 0 ≤ I) :
    δ ^ (n - 1) *
      (((A * L * δ ^ ((n - 1 : ℕ) / overlapExponent n) * I ^ (1 / (n : ℝ))) /
        (c * δ ^ (n - 1))) ^ (n : ℝ)) =
      (A / c) ^ (n : ℝ) * L ^ (n : ℝ) * I := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have he : (n - 1 : ℕ) / overlapExponent n - (n - 1 : ℕ) =
      -(n - 1 : ℕ) / (n : ℝ) := by
    rw [overlapExponent]
    field_simp
    ring
  have hratio :
      (A * L * δ ^ ((n - 1 : ℕ) / overlapExponent n) * I ^ (1 / (n : ℝ))) /
        (c * δ ^ (n - 1)) =
      (A / c) * L * δ ^ (-(n - 1 : ℕ) / (n : ℝ)) * I ^ (1 / (n : ℝ)) := by
    rw [← he, Real.rpow_sub hδ, Real.rpow_natCast]
    ring
  rw [hratio]
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hL.le,
    ← Real.rpow_mul hδ.le, ← Real.rpow_mul hI,
    one_div_mul_cancel hnR.ne', Real.rpow_one]
  have he' : (-(n - 1 : ℕ) / (n : ℝ)) * n = -(n - 1 : ℕ) :=
    div_mul_cancel₀ _ hnR.ne'
  rw [he', Real.rpow_neg hδ.le, Real.rpow_natCast]
  have hd : δ ^ (n - 1) ≠ 0 := pow_ne_zero _ hδ.ne'
  field_simp
  simp only [Real.rpow_natCast]

theorem tubeNorm_to_moment {n : ℕ} (hn : 2 ≤ n) {loss : ℝ → ℝ}
    (hloss : ∀ δ, 0 < δ → δ ≤ 1 → 0 < loss δ)
    (hTube : TubeNormBound n loss) :
    ∃ J : ℝ, 0 < J ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : Space n → ℂ, MemLp f n volume →
      (∫⁻ ω, kakeyaMaximal δ f ω ^ (n : ℝ) ∂sphereMeasure n) ≤
        ENNReal.ofReal (J * loss δ ^ (n : ℝ) * ∫ y, ‖f y‖ ^ (n : ℝ)) := by
  obtain ⟨A, c, hA, hc, hdiscrete⟩ := tubeNorm_to_discrete hn hloss hTube
  obtain ⟨U, hU, hcap⟩ := packetCap_real_upper_all_scales (n := n) (by omega)
  refine ⟨U * 32 ^ (n - 1) * ((4 : ℝ) ^ n) ^ (n : ℝ) * (A / c) ^ (n : ℝ),
    by positivity, ?_⟩
  intro δ hδ hδ1 f hf
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨m, v, hv, hsep, hcover⟩ := unit_sphere_finite_separated_net (n := n) hδ
  have hcapbound (i : Fin m) : sphereMeasure n (packetCap (32 * δ) (v i)) ≤
      ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) := by
    calc
      _ = ENNReal.ofReal ((sphereMeasure n).real (packetCap (32 * δ) (v i))) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hcap (32 * δ) (v i) (by positivity) (hv i))
  have hI : 0 ≤ ∫ y, ‖f y‖ ^ (n : ℝ) :=
    integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hsum := hdiscrete m δ hδ hδ1 v hv hsep f hf
  let B : ℝ := ((A * loss δ * δ ^ ((n - 1 : ℕ) / overlapExponent n) *
    (∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ))) / (c * δ ^ (n - 1))) ^ (n : ℝ)
  calc
    _ ≤ ∑ i, sphereMeasure n (packetCap (32 * δ) (v i)) *
        (ENNReal.ofReal ((4 : ℝ) ^ n) * kakeyaMaximal (2 * δ) f (v i)) ^ (n : ℝ) :=
      lintegral_kakeya_le_net hδ hnR.le f v hcover
    _ ≤ ∑ i, ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) *
        (ENNReal.ofReal ((4 : ℝ) ^ n) * kakeyaMaximal (2 * δ) f (v i)) ^ (n : ℝ) := by
      exact Finset.sum_le_sum fun i _ ↦ mul_le_mul' (hcapbound i) le_rfl
    _ = (ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) *
        ENNReal.ofReal ((4 : ℝ) ^ n) ^ (n : ℝ)) *
        ∑ i, kakeyaMaximal (2 * δ) f (v i) ^ (n : ℝ) := by
      simp only [ENNReal.mul_rpow_of_nonneg _ _ hnR.le, Finset.mul_sum, mul_assoc]
    _ ≤ (ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) *
        ENNReal.ofReal ((4 : ℝ) ^ n) ^ (n : ℝ)) * ENNReal.ofReal B :=
      mul_le_mul' le_rfl hsum
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hnR.le,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hscale := critical_scale_identity hn hA hc (hloss δ hδ hδ1) hδ hI
      change δ ^ (n - 1) * B = _ at hscale
      rw [mul_pow]
      calc
        (U * (32 ^ (n - 1) * δ ^ (n - 1)) * ((4 : ℝ) ^ n) ^ (n : ℝ)) * B =
            (U * 32 ^ (n - 1) * ((4 : ℝ) ^ n) ^ (n : ℝ)) * (δ ^ (n - 1) * B) := by ring
        _ = _ := by rw [hscale]; ring

theorem maximal_norm_of_moment {n : ℕ} (hn : 1 ≤ n)
    {δ J L : ℝ} (hJ : 0 < J) (hL : 0 < L)
    {f : Space n → ℂ} (hf : MemLp f n volume)
    (hmoment : (∫⁻ ω, kakeyaMaximal δ f ω ^ (n : ℝ) ∂sphereMeasure n) ≤
      ENNReal.ofReal (J * L ^ (n : ℝ) * ∫ y, ‖f y‖ ^ (n : ℝ))) :
    MemLp (kakeyaMaximal δ f) n (sphereMeasure n) ∧
      eLpNorm (kakeyaMaximal δ f) n (sphereMeasure n) ≤
        ENNReal.ofReal (J ^ (1 / (n : ℝ)) * L) * eLpNorm f n volume := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hnR.ne'
  have hI : 0 ≤ ∫ y, ‖f y‖ ^ (n : ℝ) :=
    integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hm : AEStronglyMeasurable (kakeyaMaximal δ f) (sphereMeasure n) :=
    (measurable_kakeyaMaximal δ f hf.aestronglyMeasurable).aestronglyMeasurable
  have hfnorm : ENNReal.ofReal ((∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ))) =
      eLpNorm f n volume := by
    rw [← ofReal_lpNorm hf, lpNorm_eq_integral_norm_rpow_toReal hn0 (by simp)
      hf.aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, one_div]
  have hroot : (J * L ^ (n : ℝ) * ∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ)) =
      (J ^ (1 / (n : ℝ)) * L) * (∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
    rw [Real.mul_rpow (by positivity) hI, Real.mul_rpow hJ.le (by positivity),
      ← Real.rpow_mul hL.le, mul_one_div_cancel hnR.ne', Real.rpow_one]
  have hnorm : eLpNorm (kakeyaMaximal δ f) n (sphereMeasure n) ≤
      ENNReal.ofReal (J ^ (1 / (n : ℝ)) * L) * eLpNorm f n volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hn0 (by simp) hm]
    simp only [ENNReal.toReal_natCast, enorm_eq_self]
    have h := ENNReal.rpow_le_rpow hmoment (by positivity : 0 ≤ 1 / (n : ℝ))
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), hroot,
      ENNReal.ofReal_mul (by positivity), hfnorm] at h
    exact h
  refine ⟨?_, hnorm⟩
  exact hnorm.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

/-- Conditional sharp maximal theorem for the actual Euclidean tube operator.
`hTube` is the still-unproved analytic input, explicitly visible to callers. -/
theorem sharpMaximal_of_sharpTube {n : ℕ} (hn : 2 ≤ n)
    (hTube : SharpTubeBound n) : SharpMaximalBound n := by
  obtain ⟨J, hJ, hmoment⟩ := tubeNorm_to_moment hn (fun _ ↦ logLoss_pos n)
    (sharpTube_to_norm hn hTube)
  refine ⟨J ^ (1 / (n : ℝ)), by positivity, ?_⟩
  intro δ hδ hδ1 f hf
  exact maximal_norm_of_moment (by omega) hJ (logLoss_pos n hδ hδ1) hf
    (hmoment δ hδ hδ1 f hf)

end KakeyaSharp
