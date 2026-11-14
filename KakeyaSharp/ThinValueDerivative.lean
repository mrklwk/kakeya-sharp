/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinParameterHessian
public import KakeyaSharp.VariationalStructure
public import KakeyaSharp.CompactVariation

@[expose] public section

/-! The first derivative of the actual variational supremum, conditional on
a jointly smooth family of admissible Dirichlet solutions. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp
open Set MeasureTheory KakeyaSharp.Moore KakeyaSharp.Calculus
open scoped ContDiff Matrix.Norms.Elementwise

def parameterLine (p : Space 3) (a : Fin 3) (t : ℝ) : Space 3 :=
  p + t • EuclideanSpace.single a 1

theorem hasDerivAt_parameterLine_comp {m : ℕ} {F : ThinCurrentSpace m → ℝ}
    (hF : ContDiff ℝ 1 F) (p : Space 3) (a : Fin 3) (z : ThinSpace m) (t : ℝ) :
    HasDerivAt (fun s => F (parameterLine p a s,z))
      (fderiv ℝ F (parameterLine p a t,z) (parameterDirection a)) t := by
  have hl : HasDerivAt (fun s => (parameterLine p a s,z)) (parameterDirection a) t := by
    simpa only [parameterLine, parameterDirection, id_eq, one_smul] using!
      (((hasDerivAt_id t).smul_const (EuclideanSpace.single a (1 : ℝ))).const_add p).prodMk
        (hasDerivAt_const t z)
  exact (hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hl

theorem hasDerivAt_thinParameterIntegral {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {F : ThinCurrentSpace m → ℝ} (hF : ContDiff ℝ 1 F)
    (p : Space 3) (a : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => ∫ z in thinBallAt R o, F (parameterLine p a s,z))
      (∫ z in thinBallAt R o, fderiv ℝ F (parameterLine p a t,z) (parameterDirection a)) t := by
  have hc : Continuous (fun y : ℝ × ThinSpace m => (parameterLine p a y.1,y.2)) :=
    (continuous_const.add (continuous_fst.smul continuous_const)).prodMk continuous_snd
  exact hasDerivAt_setIntegral_compact (μ := volume) (thinBallAt_measurable R o)
    (thinClosedBallAt_compact hR.le o)
    (fun z hz => show ‖z.1-o.1‖^2 + ‖z.2-o.2‖^2 ≤ R^2 from hz.le)
    (hF.continuous.comp hc)
    ((contDiff_directionalDerivative (n := 0) hF (parameterDirection a)).continuous.comp hc)
    (fun s z => hasDerivAt_parameterLine_comp hF p a z s) t

theorem thinSolution_source_linearization {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U) (hρ : ContDiff ℝ 1 ρ)
    (hb : ∀ p z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0)
    (hEq : ∀ p z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z))
    (p : Space 3) (a : Fin 3) :
    (∫ z in thinBallAt R o, U (p,z) * fderiv ℝ ρ (p,z) (parameterDirection a)) =
      (m : ℝ) * ∫ z in thinBallAt R o, thinParameterDerivative U a p z * ρ (p,z) := by
  have h := thinEnergy_linearization hR o (thinSlice_contDiff hU p)
    (thinParameterDerivative_contDiff hU a p) (hb p)
    (fun z hz => thinParameterDerivative_boundary o (hU.of_le (by norm_num)) hb p a z hz)
  convert h using 1
  · apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only [thinSlice]
    rw [thinSolution_linearized o hU hρ hEq p z hz a]
  · congr 1
    apply setIntegral_congr_fun (thinBallAt_measurable R o)
    intro z hz
    dsimp only
    rw [hEq p z hz]

theorem thinValueRealAt_PDE_representation {m : ℕ} {R : ℝ}
    (hR : 0 < R) {o : ThinSpace m} {ρ u : ThinSpace m → ℝ}
    (hρ : ContinuousOn ρ (thinClosedBallAt R o)) (hu : ThinAdmissibleAt R o u)
    (hEq : ∀ z ∈ thinBallAt R o, mooreDet m (thinQuaternionHessian u z) = ρ z) :
    thinValueRealAt R o ρ = (m : ℝ)/((m : ℝ)+1) * ∫ z in thinBallAt R o, (-u z)*ρ z := by
  rw [thinValueRealAt, thinVariationalValueAt_PDE_representation hR hρ hu hEq]
  exact EReal.toReal_coe _

theorem hasDerivAt_thinValueRealAt_parameter {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {U ρ : ThinCurrentSpace m → ℝ} (hU : ContDiff ℝ 3 U) (hρ : ContDiff ℝ 1 ρ)
    (hadm : ∀ p, ThinAdmissibleAt R o (thinSlice U p))
    (hEq : ∀ p z, z ∈ thinBallAt R o → mooreDet m (thinQuaternionHessian (thinSlice U p) z) = ρ (p,z))
    (p : Space 3) (a : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => thinValueRealAt R o (thinSlice ρ (parameterLine p a s)))
      (-(∫ z in thinBallAt R o,
        U (parameterLine p a t,z) * fderiv ℝ ρ (parameterLine p a t,z) (parameterDirection a))) t := by
  let q := parameterLine p a t
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hb : ∀ p z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → U (p,z) = 0 :=
    fun p => (hadm p).2.1
  have hlin := thinSolution_source_linearization hR o hU hρ hb hEq q a
  have hfun : (fun s => thinValueRealAt R o (thinSlice ρ (parameterLine p a s))) =
      (fun s => (m : ℝ)/((m : ℝ)+1) *
        ∫ z in thinBallAt R o, (-U (parameterLine p a s,z))*ρ (parameterLine p a s,z)) := by
    funext s
    exact thinValueRealAt_PDE_representation hR
      (thinSlice_contDiff hρ _).continuous.continuousOn (hadm _) (hEq _)
  rw [hfun]
  have hd := (hasDerivAt_thinParameterIntegral hR o (hU1.neg.mul hρ) p a t).const_mul
    ((m : ℝ)/((m : ℝ)+1))
  convert hd using 1
  have hp (z : ThinSpace m) :
      fderiv ℝ (fun y => (-U y)*ρ y) (q,z) (parameterDirection a) =
        -(thinParameterDerivative U a q z * ρ (q,z)) -
          U (q,z) * fderiv ℝ ρ (q,z) (parameterDirection a) := by
    have h := ((hU1.differentiable (by norm_num) (q,z)).hasFDerivAt.neg.mul
      (hρ.differentiable (by norm_num) (q,z)).hasFDerivAt).fderiv
    have he := congrArg (fun L => L (parameterDirection a)) h
    change fderiv ℝ (fun y => (-U y)*ρ y) (q,z) (parameterDirection a) =
      (-U (q,z)) * fderiv ℝ ρ (q,z) (parameterDirection a) +
        ρ (q,z) * (-fderiv ℝ U (q,z) (parameterDirection a)) at he
    rw [he]
    dsimp only [thinParameterDerivative]
    ring
  have hi₁ : IntegrableOn (fun z => thinParameterDerivative U a q z * ρ (q,z)) (thinBallAt R o) :=
    continuous_integrableOn_thinBallAt hR o
      ((thinParameterDerivative_contDiff hU a q).continuous.mul (thinSlice_contDiff hρ q).continuous)
  have hi₂ : IntegrableOn (fun z => U (q,z) * fderiv ℝ ρ (q,z) (parameterDirection a))
      (thinBallAt R o) := continuous_integrableOn_thinBallAt hR o
        ((thinSlice_contDiff hU q).continuous.mul
          ((contDiff_directionalDerivative (n := 0) hρ (parameterDirection a)).continuous.comp
            (continuous_const.prodMk continuous_id)))
  change -(∫ z in thinBallAt R o, U (q,z)*fderiv ℝ ρ (q,z) (parameterDirection a)) = _
  change _ = (m : ℝ)/((m : ℝ)+1) *
    ∫ z in thinBallAt R o, fderiv ℝ (fun y => (-U y)*ρ y) (q,z) (parameterDirection a)
  simp_rw [hp]
  have hiN : IntegrableOn (fun z => -(thinParameterDerivative U a q z * ρ (q,z)))
      (thinBallAt R o) := hi₁.neg
  rw [integral_sub hiN hi₂, integral_neg]
  have hm : (m : ℝ)+1 ≠ 0 := by positivity
  field_simp
  nlinarith [hlin]

end KakeyaSharp
