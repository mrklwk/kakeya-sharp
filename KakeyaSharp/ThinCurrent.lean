/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Calculus.CurrentConservation
public import KakeyaSharp.ThinPairings

@[expose] public section

/-! The actual quaternionic current on three parameter coordinates and the
thin spatial coordinates. Real-column conservation implies both transport
laws and their second-order consequence. -/
noncomputable section
namespace KakeyaSharp
open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Matrix.Norms.Elementwise

abbrev ThinCurrentSpace (m : ℕ) := Space 3 × ThinSpace m

def parameterDirection {m : ℕ} (a : Fin 3) : ThinCurrentSpace m :=
  (EuclideanSpace.single a 1, 0)

def spatialDirection {m : ℕ} (p : Fin m × Fin 3) : ThinCurrentSpace m :=
  (0, thinDirection p.1 p.2)

def currentDirection {m : ℕ} (p : Fin (m+1) × Fin 3) : ThinCurrentSpace m :=
  Fin.cases (parameterDirection p.2) (fun j => spatialDirection (j,p.2)) p.1

def currentDensity {m : ℕ}
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    (z : ThinCurrentSpace m) : ℝ := (A z 0 0).re

def currentRealFlux {m : ℕ}
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    (a : Fin 3) (p : Fin m × Fin 3) (z : ThinCurrentSpace m) : ℝ :=
  realCoefficients threeSlots (A z) (p.1.succ,p.2) (0,a)

def currentRealStress {m : ℕ}
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    (p q : Fin m × Fin 3) (z : ThinCurrentSpace m) : ℝ :=
  realCoefficients threeSlots (A z) (p.1.succ,p.2) (q.1.succ,q.2)

def RealColumnConservation {m : ℕ}
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)) : Prop :=
  ∀ z q, ∑ p, fderiv ℝ (fun y => realCoefficients threeSlots (A y) p q) z
    (currentDirection p) = 0

theorem realColumnConservation_of_strong {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hd : ∀ z j, strongDivergence threeSlots (fun p => fderiv ℝ A z (currentDirection p)) j = 0) :
    RealColumnConservation A := by
  intro z q
  simp_rw [fderiv_realCoefficient threeSlots _ _ (hA.differentiable (by norm_num) z)]
  exact realCoefficients_divergence_zero threeSlots _ (hd z) q

theorem current_time_block {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hH : ∀ z, (A z).IsHermitian) (a b : Fin 3) :
    (fun z => realCoefficients threeSlots (A z) (0,a) (0,b)) =
      if a=b then currentDensity A else fun _ => 0 := by
  funext z
  have he : A z 0 0 = ((A z 0 0).re : Quaternion ℝ) :=
    Quaternion.star_eq_self.mp ((hH z).apply 0 0)
  unfold realCoefficients
  rw [he]
  fin_cases a <;> fin_cases b <;> simp [threeSlots, currentDensity]

theorem current_mass_conservation {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hH : ∀ z, (A z).IsHermitian) (hd : RealColumnConservation A)
    (z : ThinCurrentSpace m) (b : Fin 3) :
    fderiv ℝ (currentDensity A) z (parameterDirection b) +
      ∑ p, fderiv ℝ (currentRealFlux A b p) z (spatialDirection p) = 0 := by
  have ht : (∑ a, fderiv ℝ (fun y => realCoefficients threeSlots (A y) (0,a) (0,b)) z
      (currentDirection (0,a))) = fderiv ℝ (currentDensity A) z (parameterDirection b) := by
    calc
      _ = ∑ a, if a=b then fderiv ℝ (currentDensity A) z (parameterDirection b) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [current_time_block hH a b]
        by_cases hab : a=b
        · subst b
          simp [currentDirection]
        · simp [hab, fderiv_const_apply]
      _ = _ := by simp
  have h := hd z (0,b)
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ, ht] at h
  simpa only [Fintype.sum_prod_type, currentRealFlux, currentDirection, Fin.cases_succ] using! h

theorem current_momentum_conservation {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hH : ∀ z, (A z).IsHermitian) (hd : RealColumnConservation A)
    (z : ThinCurrentSpace m) (q : Fin m × Fin 3) :
    (∑ a, fderiv ℝ (currentRealFlux A a q) z (parameterDirection a)) +
      ∑ p, fderiv ℝ (currentRealStress A p q) z (spatialDirection p) = 0 := by
  have he (a : Fin 3) :
      (fun y => realCoefficients threeSlots (A y) (0,a) (q.1.succ,q.2)) =
        currentRealFlux A a q := by
    funext y
    exact (realCoefficients_isSymm threeSlots (A y) (hH y)).apply _ _
  have h := hd z (q.1.succ,q.2)
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ] at h
  simpa only [he, Fintype.sum_prod_type, currentRealStress, currentDirection,
    Fin.cases_zero, Fin.cases_succ] using! h

theorem current_double_conservation {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 2 A) (hH : ∀ z, (A z).IsHermitian) (hd : RealColumnConservation A)
    (z : ThinCurrentSpace m) :
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
  exact Current.double_conservation parameterDirection spatialDirection (currentDensity A)
    (currentRealFlux A) (currentRealStress A) hρ hξ hS
    (current_mass_conservation hH hd) (current_momentum_conservation hH hd) z

end KakeyaSharp
