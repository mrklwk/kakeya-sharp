/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinValueSmooth
public import KakeyaSharp.ThinValueWeakLimit

@[expose] public section

/-! Constant source regularization as an actual conserved quaternionic
current: a new rank-one summand with zero spatial direction. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set Filter KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Topology Matrix.Norms.Elementwise

def currentDensityUnit (m : ℕ) : Fin (m+1) → Quaternion ℝ := Pi.single 0 1

def regularizedCurrent {m : ℕ}
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    (ε : ℝ) (y : ThinCurrentSpace m) : Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ) :=
  A y + ε • outer (currentDensityUnit m)

theorem regularizedCurrent_contDiff {m : ℕ} {n : ℕ∞ω}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ n A) (ε : ℝ) : ContDiff ℝ n (regularizedCurrent A ε) :=
  hA.add contDiff_const

theorem regularizedCurrent_isHermitian {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ∀ y, (A y).IsHermitian) (ε : ℝ) (y : ThinCurrentSpace m) :
    (regularizedCurrent A ε y).IsHermitian := by
  apply (hA y).add
  rw [Matrix.IsHermitian, quaternionMatrix_conjTranspose_real_smul,
    (outer_isHermitian (currentDensityUnit m)).eq]

theorem currentDensity_regularized {m : ℕ}
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    (ε : ℝ) (y : ThinCurrentSpace m) :
    currentDensity (regularizedCurrent A ε) y = currentDensity A y + ε := by
  simp [currentDensity, regularizedCurrent, outer, currentDensityUnit]

theorem currentFlux_regularized {m : ℕ}
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    (ε : ℝ) (y : ThinCurrentSpace m) :
    currentFlux (regularizedCurrent A ε) y = currentFlux A y := by
  funext i
  simp [currentFlux, regularizedCurrent, outer, currentDensityUnit, Fin.succ_ne_zero]

theorem currentStress_regularized {m : ℕ}
    (A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ))
    (ε : ℝ) (y : ThinCurrentSpace m) :
    currentStress (regularizedCurrent A ε) y = currentStress A y := by
  apply Matrix.ext
  intro i j
  simp [currentStress, regularizedCurrent, outer, currentDensityUnit, Fin.succ_ne_zero]

theorem regularizedCurrent_conservation {m : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hd : RealColumnConservation A) (ε : ℝ) :
    RealColumnConservation (regularizedCurrent A ε) := by
  intro y q
  have he (p : Fin (m+1) × Fin 3) :
      (fun x => realCoefficients threeSlots (regularizedCurrent A ε x) p q) =
      (fun x => realCoefficients threeSlots (A x) p q +
        realCoefficients threeSlots (ε • outer (currentDensityUnit m)) p q) := by
    funext x
    exact (realCoefficientCLM threeSlots p q).map_add _ _
  simp_rw [he, fderiv_add_const]
  exact hd y q

def regularizedWeights {m N : ℕ} (ρ : ThinCurrentSpace m → Fin N → ℝ) (ε : ℝ)
    (y : ThinCurrentSpace m) : Fin (N+1) → ℝ := Fin.cases ε (ρ y)

def regularizedDirections {m N : ℕ} (b : ThinCurrentSpace m → Fin N → Fin m → Quaternion ℝ)
    (y : ThinCurrentSpace m) : Fin (N+1) → Fin m → Quaternion ℝ := Fin.cases 0 (b y)

theorem regularizedWeights_nonneg {m N : ℕ} {ρ : ThinCurrentSpace m → Fin N → ℝ}
    {ε : ℝ} (hε : 0 ≤ ε) {y : ThinCurrentSpace m} (hρ : ∀ l, 0 ≤ ρ y l) :
    ∀ l, 0 ≤ regularizedWeights ρ ε y l := by
  intro l
  exact Fin.cases hε hρ l

theorem regularizedCurrent_mass {m N : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {ρ : ThinCurrentSpace m → Fin N → ℝ} {y : ThinCurrentSpace m}
    (hmass : currentDensity A y = ∑ l, ρ y l) (ε : ℝ) :
    currentDensity (regularizedCurrent A ε) y = ∑ l, regularizedWeights ρ ε y l := by
  rw [currentDensity_regularized, hmass]
  simp [regularizedWeights, Fin.sum_univ_succ, add_comm]

theorem currentDensity_regularized_pos {m N : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {ρ : ThinCurrentSpace m → Fin N → ℝ} {y : ThinCurrentSpace m}
    (hρ : ∀ l, 0 ≤ ρ y l) (hmass : currentDensity A y = ∑ l, ρ y l)
    {ε : ℝ} (hε : 0 < ε) : 0 < currentDensity (regularizedCurrent A ε) y := by
  rw [currentDensity_regularized, hmass]
  exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun l _ => hρ l)) hε

theorem regularizedCurrent_flux {m N : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {ρ : ThinCurrentSpace m → Fin N → ℝ} {b : ThinCurrentSpace m → Fin N → Fin m → Quaternion ℝ}
    {y : ThinCurrentSpace m} (hflux : currentFlux A y = ∑ l, ρ y l • b y l) (ε : ℝ) :
    currentFlux (regularizedCurrent A ε) y =
      ∑ l, regularizedWeights ρ ε y l • regularizedDirections b y l := by
  rw [currentFlux_regularized, hflux]
  simp [regularizedWeights, regularizedDirections, Fin.sum_univ_succ]

theorem regularizedCurrent_stress {m N : ℕ}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    {ρ : ThinCurrentSpace m → Fin N → ℝ} {b : ThinCurrentSpace m → Fin N → Fin m → Quaternion ℝ}
    {y : ThinCurrentSpace m} (hstress : currentStress A y = ∑ l, ρ y l • outer (b y l)) (ε : ℝ) :
    currentStress (regularizedCurrent A ε) y =
      ∑ l, regularizedWeights ρ ε y l • outer (regularizedDirections b y l) := by
  rw [currentStress_regularized, hstress]
  have hz : outer (0 : Fin m → Quaternion ℝ) = 0 := by
    apply Matrix.ext
    intro i j
    simp [QuaternionAlgebra.outer]
  simp [regularizedWeights, regularizedDirections, Fin.sum_univ_succ, hz]

end KakeyaSharp
