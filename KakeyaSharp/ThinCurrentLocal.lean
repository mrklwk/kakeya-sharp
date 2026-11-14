/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinCurrent
public import KakeyaSharp.Calculus.LocalConservation

@[expose] public section

/-! Quaternionic current conservation on an open set. All column equations
and Hermitian identities are used only on that set. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set Filter KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Topology Matrix.Norms.Elementwise

def RealColumnConservationOn {m : ℕ} (D : Set (ThinCurrentSpace m))
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)) : Prop :=
  ∀ z ∈ D, ∀ q, ∑ p, fderiv ℝ (fun y => realCoefficients threeSlots (A y) p q) z
    (currentDirection p) = 0

theorem realColumnConservationOn_of_strong {m : ℕ} {D : Set (ThinCurrentSpace m)}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hd : ∀ z ∈ D, ∀ j,
      strongDivergence threeSlots (fun p => fderiv ℝ A z (currentDirection p)) j = 0) :
    RealColumnConservationOn D A := by
  intro z hz q
  simp_rw [fderiv_realCoefficient threeSlots _ _ (hA.differentiable (by norm_num) z)]
  exact realCoefficients_divergence_zero threeSlots _ (hd z hz) q

theorem current_time_block_on {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {D : Set (ThinCurrentSpace m)} (hD : IsOpen D)
    (hH : ∀ z ∈ D, (A z).IsHermitian) (z : ThinCurrentSpace m) (hz : z ∈ D) (a b : Fin 3) :
    (fun y => realCoefficients threeSlots (A y) (0,a) (0,b)) =ᶠ[𝓝 z]
      if a=b then currentDensity A else fun _ => 0 := by
  filter_upwards [hD.mem_nhds hz] with y hy
  have he : A y 0 0 = ((A y 0 0).re : Quaternion ℝ) :=
    Quaternion.star_eq_self.mp ((hH y hy).apply 0 0)
  unfold realCoefficients
  rw [he]
  fin_cases a <;> fin_cases b <;> simp [threeSlots, currentDensity]

theorem current_mass_conservation_on {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {D : Set (ThinCurrentSpace m)} (hD : IsOpen D)
    (hH : ∀ z ∈ D, (A z).IsHermitian) (hd : RealColumnConservationOn D A)
    (z : ThinCurrentSpace m) (hz : z ∈ D) (b : Fin 3) :
    fderiv ℝ (currentDensity A) z (parameterDirection b) +
      ∑ p, fderiv ℝ (currentRealFlux A b p) z (spatialDirection p) = 0 := by
  have ht : (∑ a, fderiv ℝ (fun y => realCoefficients threeSlots (A y) (0,a) (0,b)) z
      (currentDirection (0,a))) = fderiv ℝ (currentDensity A) z (parameterDirection b) := by
    calc
      _ = ∑ a, if a=b then fderiv ℝ (currentDensity A) z (parameterDirection b) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [(current_time_block_on hD hH z hz a b).fderiv_eq (𝕜 := ℝ)]
        by_cases hab : a=b
        · subst b
          simp [currentDirection]
        · simp [hab, fderiv_const_apply]
      _ = _ := by simp
  have h := hd z hz (0,b)
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ, ht] at h
  simpa only [Fintype.sum_prod_type, currentRealFlux, currentDirection, Fin.cases_succ] using! h

theorem current_momentum_conservation_on {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {D : Set (ThinCurrentSpace m)} (hD : IsOpen D)
    (hH : ∀ z ∈ D, (A z).IsHermitian) (hd : RealColumnConservationOn D A)
    (z : ThinCurrentSpace m) (hz : z ∈ D) (q : Fin m × Fin 3) :
    (∑ a, fderiv ℝ (currentRealFlux A a q) z (parameterDirection a)) +
      ∑ p, fderiv ℝ (currentRealStress A p q) z (spatialDirection p) = 0 := by
  have he (a : Fin 3) :
      (fun y => realCoefficients threeSlots (A y) (0,a) (q.1.succ,q.2)) =ᶠ[𝓝 z]
        currentRealFlux A a q := by
    filter_upwards [hD.mem_nhds hz] with y hy
    exact (realCoefficients_isSymm threeSlots (A y) (hH y hy)).apply _ _
  have h := hd z hz (q.1.succ,q.2)
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ] at h
  simpa only [(he _).fderiv_eq (𝕜 := ℝ), Fintype.sum_prod_type, currentRealStress, currentDirection,
    Fin.cases_zero, Fin.cases_succ] using! h

theorem current_double_conservation_on {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 2 A) {D : Set (ThinCurrentSpace m)} (hD : IsOpen D)
    (hH : ∀ z ∈ D, (A z).IsHermitian) (hd : RealColumnConservationOn D A)
    (z : ThinCurrentSpace m) (hz : z ∈ D) :
    (∑ a, fderiv ℝ (fderiv ℝ (currentDensity A)) z (parameterDirection a) (parameterDirection a)) =
      ∑ p, ∑ q, fderiv ℝ (fderiv ℝ (currentRealStress A q p)) z
        (spatialDirection p) (spatialDirection q) := by
  have hρ : ContDiff ℝ 2 (currentDensity A) := by
    have h := (realCoefficientCLM threeSlots (0,0) (0,0)).contDiff.comp hA
    change ContDiff ℝ 2 (fun z => realCoefficients threeSlots (A z) (0,0) (0,0)) at h
    simpa only [realCoefficients, threeSlots, Matrix.cons_val_zero, star_one, one_mul, mul_one,
      currentDensity] using! h
  have hξ (a : Fin 3) (p : Fin m × Fin 3) : ContDiff ℝ 2 (currentRealFlux A a p) :=
    (realCoefficientCLM threeSlots (p.1.succ,p.2) (0,a)).contDiff.comp hA
  have hS (p q : Fin m × Fin 3) : ContDiff ℝ 2 (currentRealStress A p q) :=
    (realCoefficientCLM threeSlots (p.1.succ,p.2) (q.1.succ,q.2)).contDiff.comp hA
  exact Current.double_conservation_on hD parameterDirection spatialDirection (currentDensity A)
    (currentRealFlux A) (currentRealStress A) hρ hξ hS
    (current_mass_conservation_on hD hH hd) (current_momentum_conservation_on hD hH hd) z hz


end KakeyaSharp
