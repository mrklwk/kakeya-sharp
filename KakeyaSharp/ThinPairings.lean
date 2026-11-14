/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.QuaternionGreen
public import KakeyaSharp.ThinSecondVariation

@[expose] public section

/-! The full cofactor pairing and cancellation of the three parameter directions. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

theorem thinCofactor_tested_pairing {m : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) (L : Quaternion ℝ →L[ℝ] ℝ)
    {ψ u v : ThinSpace m → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hzu : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → u z = 0) :
    (∫ z in thinBallAt R o, L (quaternionPairing (thinCofactor ψ z)
      (thinQuaternionGradient u z) (thinQuaternionGradient v z))) =
      L 1 * (-(∫ z in thinBallAt R o, u z * mooreDifferential m
        (thinQuaternionHessian ψ z) (thinQuaternionHessian v z))) := by
  let : (volume : Measure (ThinSpace m)).IsAddHaarMeasure := by
    change ((volume : Measure (Space m)).prod (volume : Measure (ThinTransverseSpace m))).IsAddHaarMeasure
    infer_instance
  exact moore_cofactor_pairing_bounded threeSlots (fun p => thinDirection p.1 p.2) L
    (thinBallAt_isOpen R o) (thinBallAt_bounded hR.le o) (thinBallAt_null_frontier R o)
    hψ hu hv (fun z hz => hzu z (thinBallAt_frontier_subset R o hz))

theorem thinQuaternionGradient_continuous {m : ℕ} {g : ThinSpace m → ℝ}
    (hg : ContDiff ℝ 2 g) : Continuous (thinQuaternionGradient g) := by
  apply continuous_pi
  intro i
  unfold thinQuaternionGradient gradientMap
  apply continuous_finsetSum
  intro α _
  exact (((hg.fderiv_right (m := 1) (by norm_num)).continuous).clm_apply
    continuous_const).smul continuous_const

theorem continuous_quaternionPairing {X : Type*} [TopologicalSpace X] {m : ℕ}
    {A : X → Matrix (Fin m) (Fin m) (Quaternion ℝ)}
    {u v : X → Fin m → Quaternion ℝ} (hA : Continuous A)
    (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun z => quaternionPairing (A z) (u z) (v z)) := by
  unfold quaternionPairing
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((continuous_star.comp ((continuous_apply i).comp hu)).mul
    ((continuous_apply j).comp ((continuous_apply i).comp hA))).mul
    ((continuous_apply j).comp hv)

def thinParameterGradient {m : ℕ} (g : Fin 3 → ThinSpace m → ℝ)
    (z : ThinSpace m) (i : Fin m) : Quaternion ℝ :=
  ∑ β, thinQuaternionGradient (g β) z i * star (threeSlots β)

theorem thinCofactor_three_pairings {m : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) {ψ : ThinSpace m → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (g : Fin 3 → ThinSpace m → ℝ) (hg : ∀ β, ContDiff ℝ 2 (g β))
    (hzg : ∀ β z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → g β z = 0) :
    (∫ z in thinBallAt R o, quaternionForm (thinCofactor ψ z) (thinParameterGradient g z)) =
      ∑ β, ∫ z in thinBallAt R o,
        quaternionForm (thinCofactor ψ z) (thinQuaternionGradient (g β) z) := by
  have hC : Continuous (thinCofactor ψ) :=
    ((contDiff_mooreCofactor m 1).comp
      (contDiff_directionalHessian_one threeSlots (fun p => thinDirection p.1 p.2) hψ)).continuous
  let f := fun (a b : Fin 3) (z : ThinSpace m) =>
    (threeSlots a * quaternionPairing (thinCofactor ψ z)
      (thinQuaternionGradient (g a) z) (thinQuaternionGradient (g b) z) * star (threeSlots b)).re
  have hi (a b : Fin 3) : IntegrableOn (f a b) (thinBallAt R o) := by
    apply continuous_integrableOn_thinBallAt hR o
    exact (quaternionSandwichCLM (threeSlots a) (star (threeSlots b))).continuous.comp
      (continuous_quaternionPairing hC (thinQuaternionGradient_continuous (hg a))
        (thinQuaternionGradient_continuous (hg b)))
  have he (a b : Fin 3) : (∫ z in thinBallAt R o, f a b z) =
      (if a=b then 1 else 0) * (-(∫ z in thinBallAt R o, g a z *
        mooreDifferential m (thinQuaternionHessian ψ z) (thinQuaternionHessian (g b) z))) := by
    have h := thinCofactor_tested_pairing hR o
      (quaternionSandwichCLM (threeSlots a) (star (threeSlots b)))
      hψ ((hg a).of_le (by norm_num)) (hg b) (hzg a)
    simpa only [quaternionSandwichCLM_apply, mul_one, threeSlots_orthonormal] using h
  have hd (β : Fin 3) : (∫ z in thinBallAt R o,
      quaternionForm (thinCofactor ψ z) (thinQuaternionGradient (g β) z)) =
      -(∫ z in thinBallAt R o, g β z * mooreDifferential m
        (thinQuaternionHessian ψ z) (thinQuaternionHessian (g β) z)) := by
    rw [← thinCofactor_energy_identity hR o hψ (hg β) (hzg β)]
    simp_rw [neg_mul, integral_neg]
  have hp (z : ThinSpace m) :
      quaternionForm (thinCofactor ψ z) (thinParameterGradient g z) = ∑ a, ∑ b, f a b z :=
    quaternionForm_sum_right_mul _ _ threeSlots
  simp_rw [hp]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hi _ b), he]
  simp [ite_mul, hd]

end KakeyaSharp
