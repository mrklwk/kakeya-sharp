/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.QuaternionPairing

@[expose] public section

/-! The zero-boundary Green identity tested against every real linear
functional on the quaternions, not just the real-part projection. -/
noncomputable section
namespace KakeyaSharp.Green
open Matrix Set Filter MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped Topology ContDiff Matrix.Norms.Elementwise

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype I] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem real_operator_green_bounded {S : Set E} (hS : IsOpen S)
    (hb : Bornology.IsBounded S) (hnull : μ (frontier S) = 0)
    (d : I → E) (K : I → I → E → ℝ) {u v : E → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (d i) = 0) :
    (∫ x in S, u x * (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x (d i) (d j)) ∂μ) =
      -(∫ x in S, ∑ i, ∑ j, K i j x * fderiv ℝ u x (d i) * fderiv ℝ v x (d j) ∂μ) := by
  obtain ⟨u',hu',hsu,heu⟩ := exists_compact_extension_on_bounded hb hu
  obtain ⟨v',hv',hsv,hev⟩ := exists_compact_extension_on_bounded hb hv
  have hzu : ∀ x ∈ frontier S, u' x = 0 := by
    intro x hx
    rw [(heu x hx.1).self_of_nhds, hz x hx]
  have h := real_operator_green_zero_boundary hS hnull d K hK hu' hv' hsu hsv hzu hdiv
  have hleft : (∫ x in S, u' x * (∑ i, ∑ j, K i j x *
      fderiv ℝ (fderiv ℝ v') x (d i) (d j)) ∂μ) =
      ∫ x in S, u x * (∑ i, ∑ j, K i j x *
        fderiv ℝ (fderiv ℝ v) x (d i) (d j)) ∂μ := by
    apply setIntegral_congr_fun hS.measurableSet
    intro x hx
    dsimp only
    rw [(heu x (subset_closure hx)).self_of_nhds,
      ((hev x (subset_closure hx)).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
  have hright : (∫ x in S, ∑ i, ∑ j, K i j x *
      fderiv ℝ u' x (d i) * fderiv ℝ v' x (d j) ∂μ) =
      ∫ x in S, ∑ i, ∑ j, K i j x *
        fderiv ℝ u x (d i) * fderiv ℝ v x (d j) ∂μ := by
    apply setIntegral_congr_fun hS.measurableSet
    intro x hx
    dsimp only
    rw [(heu x (subset_closure hx)).fderiv_eq (𝕜 := ℝ),
      (hev x (subset_closure hx)).fderiv_eq (𝕜 := ℝ)]
  rwa [hleft, hright] at h

theorem quaternion_current_pairing_bounded {n s : ℕ}
    (e : Fin s → Quaternion ℝ) (d : Fin n × Fin s → E)
    (L : Quaternion ℝ →L[ℝ] ℝ) {S : Set E}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : μ (frontier S) = 0)
    {A : E → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hHerm : ∀ x, (A x).IsHermitian)
    (hdiv : ∀ x b, strongDivergence e (fun p => fderiv ℝ A x (d p)) b = 0)
    {u v : E → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, L (quaternionPairing (A x)
      (gradientMap e (directionalGradient d u x))
      (gradientMap e (directionalGradient d v x))) ∂μ) =
      L 1 * (-(∫ x in S, u x * realTrace (A x * directionalHessian e d v x) ∂μ)) := by
  let K := fun p q x => testedCoefficientCLM e L p q (A x)
  have hK (p q : Fin n × Fin s) : ContDiff ℝ 1 (K p q) :=
    (testedCoefficientCLM e L p q).contDiff.comp hA
  have hd (x : E) (q : Fin n × Fin s) : ∑ p, fderiv ℝ (K p q) x (d p) = 0 := by
    have hder (p : Fin n × Fin s) : fderiv ℝ (K p q) x (d p) =
        testedCoefficientCLM e L p q (fderiv ℝ A x (d p)) := by
      exact congrArg (fun T => T (d p))
        (((testedCoefficientCLM e L p q).hasFDerivAt.comp x
          ((hA.differentiable (by norm_num) x).hasFDerivAt)).fderiv)
    simp_rw [hder]
    exact testedCoefficients_divergence_zero e L _ (hdiv x) q
  have h := real_operator_green_bounded hS hb hnull d K hK hu hv hz hd
  have he (x : E) : (∑ p, ∑ q, K p q x * fderiv ℝ (fderiv ℝ v) x (d p) (d q)) =
      realTrace (A x * directionalHessian e d v x) * L 1 :=
    tested_hessian_contraction e L (hHerm x) _ (directionalRealHessian_isSymm d hv.contDiffAt)
  have hp (x : E) : (∑ p, ∑ q, K p q x * fderiv ℝ u x (d p) * fderiv ℝ v x (d q)) =
      L (quaternionPairing (A x) (gradientMap e (directionalGradient d u x))
        (gradientMap e (directionalGradient d v x))) :=
    (tested_pairing_gradient e L _ _ _).symm
  simp_rw [he, hp, ← mul_assoc] at h
  rw [integral_mul_const] at h
  linarith

theorem moore_cofactor_pairing_bounded {n s : ℕ}
    (e : Fin s → Quaternion ℝ) (d : Fin n × Fin s → E)
    (L : Quaternion ℝ →L[ℝ] ℝ) {S : Set E}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : μ (frontier S) = 0)
    {ψ u v : E → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, L (quaternionPairing (mooreCofactor n (directionalHessian e d ψ x))
      (gradientMap e (directionalGradient d u x))
      (gradientMap e (directionalGradient d v x))) ∂μ) =
      L 1 * (-(∫ x in S, u x * mooreDifferential n (directionalHessian e d ψ x)
        (directionalHessian e d v x) ∂μ)) := by
  have hA : ContDiff ℝ 1 (fun x => mooreCofactor n (directionalHessian e d ψ x)) :=
    (contDiff_mooreCofactor n 1).comp (contDiff_directionalHessian_one e d hψ)
  have h := quaternion_current_pairing_bounded e d L hS hb hnull hA
    (fun x => mooreCofactor_isHermitian n _) (fun x b =>
      mooreCofactor_directionalHessian_divergence e d hψ.contDiffAt b) hu hv hz
  simpa only [mooreCofactor_pairing n _ _ (directionalHessian_isHermitian e d hv.contDiffAt)] using h

end KakeyaSharp.Green
