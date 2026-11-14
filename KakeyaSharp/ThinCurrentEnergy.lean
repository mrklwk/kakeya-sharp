/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinCrossPairing
public import KakeyaSharp.CurrentSquare

@[expose] public section

/-! The integrated current energy inequality. The linearized determinant
equation combined with mass conservation is explicit in `hlaw`; deriving
it from a smooth parameter-dependent Dirichlet family is a separate step. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

theorem continuous_realTrace_mul {X : Type*} [TopologicalSpace X] {m : ℕ}
    {A B : X → Matrix (Fin m) (Fin m) (Quaternion ℝ)}
    (hA : Continuous A) (hB : Continuous B) : Continuous (fun x => realTrace (A x * B x)) := by
  apply Quaternion.continuous_re.comp
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (((continuous_apply j).comp ((continuous_apply i).comp hA)).mul
    ((continuous_apply i).comp ((continuous_apply j).comp hB)))

theorem thinParameterGradient_continuous {m : ℕ} {g : Fin 3 → ThinSpace m → ℝ}
    (hg : ∀ β, ContDiff ℝ 2 (g β)) : Continuous (thinParameterGradient g) := by
  apply continuous_pi
  intro i
  unfold thinParameterGradient
  apply continuous_finsetSum
  intro β _
  exact (((continuous_apply i).comp (thinQuaternionGradient_continuous (hg β))).mul continuous_const)

theorem thinCurrent_energy_le_stress {m N : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {ψ : ThinSpace m → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hpos : ∀ z ∈ thinBallAt R o, ∀ w ≠ 0, 0 < quaternionForm (thinQuaternionHessian ψ z) w)
    (g : Fin 3 → ThinSpace m → ℝ) (hg : ∀ β, ContDiff ℝ 2 (g β))
    (hzg : ∀ β z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → g β z = 0)
    (ξ : ThinSpace m → Fin m → Quaternion ℝ) (hξ : ContDiff ℝ 1 ξ)
    (S : ThinSpace m → Matrix (Fin m) (Fin m) (Quaternion ℝ)) (hS : Continuous S)
    (ρ : ThinSpace m → Fin N → ℝ) (b : ThinSpace m → Fin N → Fin m → Quaternion ℝ)
    (hρ : ∀ z ∈ thinBallAt R o, ∀ l, 0 ≤ ρ z l)
    (hmass : ∀ z ∈ thinBallAt R o, mooreDet m (thinQuaternionHessian ψ z) = ∑ l, ρ z l)
    (hflux : ∀ z ∈ thinBallAt R o, ξ z = ∑ l, ρ z l • b z l)
    (hstress : ∀ z ∈ thinBallAt R o, S z = ∑ l, ρ z l • outer (b z l))
    (hlaw : ∀ β z, z ∈ thinBallAt R o →
      mooreDifferential m (thinQuaternionHessian ψ z) (thinQuaternionHessian (g β) z) +
        ∑ p, fderiv ℝ (thinVectorFlux ξ β p) z (thinDirection p.1 p.2) = 0) :
    (∑ β, ∫ z in thinBallAt R o,
      quaternionForm (thinCofactor ψ z) (thinQuaternionGradient (g β) z)) ≤
      ∫ z in thinBallAt R o, realTrace (S z * thinQuaternionHessian ψ z) := by
  have hC : Continuous (thinCofactor ψ) :=
    ((contDiff_mooreCofactor m 1).comp
      (contDiff_directionalHessian_one threeSlots (fun p => thinDirection p.1 p.2) hψ)).continuous
  have hW := thinParameterGradient_continuous hg
  have hiS : IntegrableOn (fun z => realTrace (S z * thinQuaternionHessian ψ z)) (thinBallAt R o) :=
    continuous_integrableOn_thinBallAt hR o (continuous_realTrace_mul hS (thinHessian_continuous hψ))
  have hiQ : IntegrableOn (fun z => quaternionForm (thinCofactor ψ z) (thinParameterGradient g z))
      (thinBallAt R o) := by
    apply continuous_integrableOn_thinBallAt hR o
    have h := Quaternion.continuous_re.comp (continuous_quaternionPairing hC hW hW)
    simpa only [Function.comp_def, quaternionPairing_re] using h
  have hiX : IntegrableOn (fun z => (star (thinParameterGradient g z) ⬝ᵥ ξ z).re)
      (thinBallAt R o) := by
    apply continuous_integrableOn_thinBallAt hR o
    apply Quaternion.continuous_re.comp
    unfold dotProduct
    apply continuous_finsetSum
    intro i _
    exact ((continuous_star.comp ((continuous_apply i).comp hW)).mul
      ((continuous_apply i).comp hξ.continuous))
  have hI : 0 ≤ ∫ z in thinBallAt R o,
      realTrace (S z * thinQuaternionHessian ψ z) +
        quaternionForm (thinCofactor ψ z) (thinParameterGradient g z) +
          2 * (star (thinParameterGradient g z) ⬝ᵥ ξ z).re := by
    apply setIntegral_nonneg (thinBallAt_measurable R o)
    intro z hz
    obtain ⟨V,hHV,hVH⟩ := exists_quaternion_inverse_of_pos (thinQuaternionHessian ψ z) (hpos z hz)
    have hnonneg (w : Fin m → Quaternion ℝ) : 0 ≤ quaternionForm (thinQuaternionHessian ψ z) w := by
      by_cases hw : w=0
      · subst w
        simp [quaternionForm]
      · exact (hpos z hz w hw).le
    have h := current_square_nonneg (thinQuaternionHessian ψ z) V
      (thinQuaternionHessian_isHermitian (hψ.contDiffAt.of_le (by norm_num))) hHV hVH hnonneg
      (ρ z) (hρ z hz) (b z) (hmass z hz) (thinParameterGradient g z)
    simpa only [← hflux z hz, ← hstress z hz, thinCofactor] using h
  have hiSQ : IntegrableOn (fun z => realTrace (S z * thinQuaternionHessian ψ z) +
      quaternionForm (thinCofactor ψ z) (thinParameterGradient g z)) (thinBallAt R o) := hiS.add hiQ
  rw [integral_add hiSQ (hiX.const_mul 2), integral_add hiS hiQ,
    integral_const_mul, thinCofactor_three_pairings hR o hψ g hg hzg,
    thinCofactor_cross_pairing hR o hψ g hg hzg ξ hξ hlaw] at hI
  linarith

end KakeyaSharp
