/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.BoundaryGreen
public import KakeyaSharp.Calculus.CofactorDivergence

@[expose] public section

/-! Green identities for the actual Moore cofactor along arbitrary fixed directions.
The domain is bounded and open with null boundary. The only boundary condition
on the first test is its value; no derivative boundary condition is imposed. -/

noncomputable section
namespace KakeyaSharp.Green
open Matrix Set Filter MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped Topology ContDiff Matrix.Norms.Elementwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n s : ℕ}

def directionalGradient (d : Fin n × Fin s → E) (u : E → ℝ) (x : E)
    (p : Fin n × Fin s) : ℝ := fderiv ℝ u x (d p)

theorem directionalRealHessian_isSymm (d : Fin n × Fin s → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    (directionalRealHessian d u x).IsSymm := by
  ext p q
  exact (hu.isSymmSndFDerivAt (by norm_num)).eq (d q) (d p)

theorem directionalHessian_isHermitian (e : Fin s → Quaternion ℝ)
    (d : Fin n × Fin s → E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) : (directionalHessian e d u x).IsHermitian :=
  hessianMap_isHermitian e _ (directionalRealHessian_isSymm d hu)

theorem contDiff_directionalHessian_one (e : Fin s → Quaternion ℝ)
    (d : Fin n × Fin s → E) {u : E → ℝ} (hu : ContDiff ℝ 3 u) :
    ContDiff ℝ 1 (directionalHessian e d u) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hH : ContDiff ℝ 1 (directionalRealHessian d u) := by
    apply contDiff_pi.mpr
    intro p
    apply contDiff_pi.mpr
    intro q
    exact (hD.clm_apply contDiff_const).clm_apply contDiff_const
  exact (hessianCLM e).contDiff.comp hH

theorem fderiv_realCoefficient (e : Fin s → Quaternion ℝ) (p q : Fin n × Fin s)
    {A : E → Matrix (Fin n) (Fin n) (Quaternion ℝ)} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : E) :
    fderiv ℝ (fun y => realCoefficients e (A y) p q) x v =
      realCoefficients e (fderiv ℝ A x v) p q := by
  have h := ((realCoefficientCLM e p q).hasFDerivAt.comp x hA.hasFDerivAt).fderiv
  exact congrArg (fun L => L v) h

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]

theorem directional_current_green_zero_boundary
    (e : Fin s → Quaternion ℝ) (d : Fin n × Fin s → E) {S : Set E}
    (hS : IsOpen S) (hnull : μ (frontier S) = 0)
    {A : E → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hdiv : ∀ x b, strongDivergence e (fun p => fderiv ℝ A x (d p)) b = 0)
    {u v : E → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hsu : HasCompactSupport u) (hsv : HasCompactSupport v)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, u x * realTrace (A x * directionalHessian e d v x) ∂μ) =
      -(∫ x in S, ∑ p, ∑ q, realCoefficients e (A x) p q *
        directionalGradient d u x p * directionalGradient d v x q ∂μ) := by
  have hK (p q : Fin n × Fin s) :
      ContDiff ℝ 1 (fun x => realCoefficients e (A x) p q) :=
    (realCoefficientCLM e p q).contDiff.comp hA
  have hd (x : E) (q : Fin n × Fin s) :
      ∑ p, fderiv ℝ (fun y => realCoefficients e (A y) p q) x (d p) = 0 := by
    simp_rw [fderiv_realCoefficient e _ _ (hA.differentiable (by norm_num) x)]
    exact realCoefficients_divergence_zero e _ (hdiv x) q
  have h := real_operator_green_zero_boundary hS hnull d
    (fun p q x => realCoefficients e (A x) p q) hK hu hv hsu hsv hz hd
  have he (x : E) : realTrace (A x * directionalHessian e d v x) =
      ∑ p, ∑ q, realCoefficients e (A x) p q * directionalRealHessian d v x p q :=
    realTrace_hessianMap (A x) e _ (directionalRealHessian_isSymm d hv.contDiffAt)
  simpa only [he, directionalRealHessian, directionalGradient] using h

theorem exists_compact_extension_on_bounded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : Bornology.IsBounded S) {k : ℕ∞}
    {u : E → ℝ} (hu : ContDiff ℝ k u) :
    ∃ v : E → ℝ, ContDiff ℝ k v ∧ HasCompactSupport v ∧
      ∀ x ∈ closure S, v =ᶠ[𝓝 x] u := by
  obtain ⟨R,hR,hsub⟩ := hS.closure.subset_ball_lt 0 (0 : E)
  let b : ContDiffBump (0 : E) := ⟨R,R+1,hR,lt_add_one R⟩
  refine ⟨fun x ↦ b x * u x, b.contDiff.mul hu, b.hasCompactSupport.mul_right, ?_⟩
  intro x hx
  filter_upwards [b.eventuallyEq_one_of_mem_ball (hsub hx)] with y hy
  change b y = 1 at hy
  rw [hy, one_mul]


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem directionalGradient_congr_nhds (d : Fin n × Fin s → E)
    {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    directionalGradient d u x = directionalGradient d v x := by
  funext p
  exact congrArg (fun D => D (d p)) (h.fderiv_eq (𝕜 := ℝ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem directionalHessian_congr_nhds (e : Fin s → Quaternion ℝ)
    (d : Fin n × Fin s → E) {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    directionalHessian e d u x = directionalHessian e d v x := by
  have he := (h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  unfold directionalHessian directionalRealHessian
  rw [he]

theorem directional_current_green_bounded
    (e : Fin s → Quaternion ℝ) (d : Fin n × Fin s → E) {S : Set E}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : μ (frontier S) = 0)
    {A : E → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hdiv : ∀ x b, strongDivergence e (fun p => fderiv ℝ A x (d p)) b = 0)
    {u v : E → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, u x * realTrace (A x * directionalHessian e d v x) ∂μ) =
      -(∫ x in S, ∑ p, ∑ q, realCoefficients e (A x) p q *
        directionalGradient d u x p * directionalGradient d v x q ∂μ) := by
  obtain ⟨u',hu',hsu,heu⟩ := exists_compact_extension_on_bounded hb hu
  obtain ⟨v',hv',hsv,hev⟩ := exists_compact_extension_on_bounded hb hv
  have hzu : ∀ x ∈ frontier S, u' x = 0 := by
    intro x hx
    rw [(heu x hx.1).self_of_nhds, hz x hx]
  calc
    _ = ∫ x in S, u' x * realTrace (A x * directionalHessian e d v' x) ∂μ := by
      apply setIntegral_congr_fun hS.measurableSet
      intro x hx
      dsimp only
      rw [(heu x (subset_closure hx)).self_of_nhds,
        directionalHessian_congr_nhds e d (hev x (subset_closure hx))]
    _ = -(∫ x in S, ∑ p, ∑ q, realCoefficients e (A x) p q *
        directionalGradient d u' x p * directionalGradient d v' x q ∂μ) :=
      directional_current_green_zero_boundary e d hS hnull hA hdiv hu' hv' hsu hsv hzu
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun hS.measurableSet
      intro x hx
      dsimp only
      rw [directionalGradient_congr_nhds d (heu x (subset_closure hx)),
        directionalGradient_congr_nhds d (hev x (subset_closure hx))]

theorem moore_cofactor_green_bounded
    (e : Fin s → Quaternion ℝ) (d : Fin n × Fin s → E) {S : Set E}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : μ (frontier S) = 0)
    {ψ u v : E → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, u x * mooreDifferential n (directionalHessian e d ψ x)
        (directionalHessian e d v x) ∂μ) =
      -(∫ x in S, ∑ p, ∑ q,
        realCoefficients e (mooreCofactor n (directionalHessian e d ψ x)) p q *
          directionalGradient d u x p * directionalGradient d v x q ∂μ) := by
  have hA : ContDiff ℝ 1 (fun x => mooreCofactor n (directionalHessian e d ψ x)) :=
    (contDiff_mooreCofactor n 1).comp (contDiff_directionalHessian_one e d hψ)
  have h := directional_current_green_bounded e d hS hb hnull hA
    (fun x b => mooreCofactor_directionalHessian_divergence e d hψ.contDiffAt b) hu hv hz
  simpa only [mooreCofactor_pairing n _ _ (directionalHessian_isHermitian e d hv.contDiffAt)] using h

end KakeyaSharp.Green

