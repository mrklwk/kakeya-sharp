/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.CurrentIntegrals
public import KakeyaSharp.ThinPairings

@[expose] public section

/-! The integrated mixed pairing from the linearized conservation equation. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

theorem gradient_flux_coefficients {m s : ℕ} (e : Fin s → Quaternion ℝ)
    (a : Quaternion ℝ) (v : Fin m × Fin s → ℝ) (ξ : Fin m → Quaternion ℝ) :
    (∑ i, (a * star (gradientMap e v i) * ξ i).re) =
      ∑ p, v p * (star (e p.2) * ξ p.1 * a).re := by
  simp only [gradientMap, star_sum, Quaternion.star_smul, Finset.mul_sum,
    Finset.sum_mul, mul_smul_comm, smul_mul_assoc, quaternion_re_sum,
    Quaternion.re_smul, smul_eq_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro α _
  rw [mul_assoc a, quaternion_re_mul_comm a]

def thinVectorFlux {m : ℕ} (ξ : ThinSpace m → Fin m → Quaternion ℝ)
    (β : Fin 3) (p : Fin m × Fin 3) (z : ThinSpace m) : ℝ :=
  (star (threeSlots p.2) * ξ z p.1 * threeSlots β).re

theorem thinParameterGradient_flux {m : ℕ} (g : Fin 3 → ThinSpace m → ℝ)
    (ξ : ThinSpace m → Fin m → Quaternion ℝ) (z : ThinSpace m) :
    (star (thinParameterGradient g z) ⬝ᵥ ξ z).re =
      ∑ β, ∑ p, fderiv ℝ (g β) z (thinDirection p.1 p.2) * thinVectorFlux ξ β p z := by
  simp only [dotProduct, Pi.star_apply, thinParameterGradient, star_sum, star_mul,
    star_star, Finset.sum_mul, quaternion_re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  exact gradient_flux_coefficients threeSlots (threeSlots β) _ (ξ z)

theorem thinVectorFlux_contDiff {m : ℕ} {ξ : ThinSpace m → Fin m → Quaternion ℝ}
    (hξ : ContDiff ℝ 1 ξ) (β : Fin 3) (p : Fin m × Fin 3) :
    ContDiff ℝ 1 (thinVectorFlux ξ β p) :=
  (quaternionSandwichCLM (star (threeSlots p.2)) (threeSlots β)).contDiff.comp
    ((contDiff_pi.mp hξ) p.1)

theorem thinCofactor_cross_pairing {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {ψ : ThinSpace m → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (g : Fin 3 → ThinSpace m → ℝ) (hg : ∀ β, ContDiff ℝ 2 (g β))
    (hzg : ∀ β z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → g β z = 0)
    (ξ : ThinSpace m → Fin m → Quaternion ℝ) (hξ : ContDiff ℝ 1 ξ)
    (hlaw : ∀ β z, z ∈ thinBallAt R o →
      mooreDifferential m (thinQuaternionHessian ψ z) (thinQuaternionHessian (g β) z) +
        ∑ p, fderiv ℝ (thinVectorFlux ξ β p) z (thinDirection p.1 p.2) = 0) :
    (∫ z in thinBallAt R o, (star (thinParameterGradient g z) ⬝ᵥ ξ z).re) =
      -(∑ β, ∫ z in thinBallAt R o,
        quaternionForm (thinCofactor ψ z) (thinQuaternionGradient (g β) z)) := by
  let : (volume : Measure (ThinSpace m)).IsAddHaarMeasure := by
    change ((volume : Measure (Space m)).prod (volume : Measure (ThinTransverseSpace m))).IsAddHaarMeasure
    infer_instance
  have he (β : Fin 3) : (∫ z in thinBallAt R o, g β z *
      mooreDifferential m (thinQuaternionHessian ψ z) (thinQuaternionHessian (g β) z)) =
      ∫ z in thinBallAt R o, ∑ p,
        fderiv ℝ (g β) z (thinDirection p.1 p.2) * thinVectorFlux ξ β p z := by
    calc
      _ = -(∫ z in thinBallAt R o, g β z *
          (∑ p, fderiv ℝ (thinVectorFlux ξ β p) z (thinDirection p.1 p.2))) := by
        rw [← integral_neg]
        apply setIntegral_congr_fun (thinBallAt_measurable R o)
        intro z hz
        dsimp only
        have h := hlaw β z hz
        have hh : mooreDifferential m (thinQuaternionHessian ψ z)
            (thinQuaternionHessian (g β) z) =
            -(∑ p, fderiv ℝ (thinVectorFlux ξ β p) z (thinDirection p.1 p.2)) := by linarith
        rw [hh, mul_neg]
      _ = _ := by
        rw [integral_divergence_by_parts_bounded (thinBallAt_isOpen R o)
          (thinBallAt_bounded hR.le o) (thinBallAt_null_frontier R o)
          ((hg β).of_le (by norm_num)) (fun z hz => hzg β z (thinBallAt_frontier_subset R o hz))
          (fun p => thinDirection p.1 p.2) (thinVectorFlux ξ β)
          (thinVectorFlux_contDiff hξ β), neg_neg]
  have hq (β : Fin 3) : (∫ z in thinBallAt R o, g β z *
      mooreDifferential m (thinQuaternionHessian ψ z) (thinQuaternionHessian (g β) z)) =
      -(∫ z in thinBallAt R o,
        quaternionForm (thinCofactor ψ z) (thinQuaternionGradient (g β) z)) := by
    have h := thinCofactor_energy_identity hR o hψ (hg β) (hzg β)
    simp only [neg_mul, integral_neg] at h
    linarith
  have hi (β : Fin 3) : IntegrableOn (fun z => ∑ p,
      fderiv ℝ (g β) z (thinDirection p.1 p.2) * thinVectorFlux ξ β p z) (thinBallAt R o) := by
    apply continuous_integrableOn_thinBallAt hR o
    apply continuous_finsetSum
    intro p _
    exact (continuous_directional ((hg β).of_le (by norm_num)) _).mul
      (thinVectorFlux_contDiff hξ β p).continuous
  simp_rw [thinParameterGradient_flux]
  rw [integral_finsetSum _ (fun β _ => hi β)]
  simp_rw [← he, hq]
  simp only [Finset.sum_neg_distrib]

end KakeyaSharp
