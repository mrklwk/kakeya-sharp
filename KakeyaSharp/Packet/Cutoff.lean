/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinCurrentLocal

@[expose] public section

/-! The exact product rule for a scalar cutoff of a quaternionic current.
Tangency to its rank-one column makes the differentiated cutoff vanish. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp.Packet
open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Green
open scoped Matrix.Norms.Elementwise

def columnContraction {n s : ℕ} (e : Fin s → Q) (ξ : Fin n × Fin s → ℝ)
    (A : Matrix (Fin n) (Fin n) Q) (b : Fin n) : Q :=
  ∑ a, ∑ α, ξ (a,α) • (star (e α)*A a b)

theorem columnContraction_outer {n s : ℕ} (e : Fin s → Q)
    (ξ : Fin n × Fin s → ℝ) (B : Fin n → Q) (b : Fin n) :
    columnContraction e ξ (outer B) b =
      star (∑ a, star (B a)*gradientMap e ξ a)*star (B b) := by
  simp only [columnContraction, outer, gradientMap, star_sum, star_mul, star_star,
    Quaternion.star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    mul_assoc]

theorem columnContraction_smul {n s : ℕ} (e : Fin s → Q)
    (ξ : Fin n × Fin s → ℝ) (A : Matrix (Fin n) (Fin n) Q) (f : ℝ) (b : Fin n) :
    columnContraction e ξ (f • A) b = f • columnContraction e ξ A b := by
  simp only [columnContraction, Matrix.smul_apply, mul_smul_comm, smul_comm f,
    Finset.smul_sum]

theorem strongDivergence_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n s : ℕ} (e : Fin s → Q) (d : Fin n × Fin s → E)
    {f : E → ℝ} {A : E → Matrix (Fin n) (Fin n) Q} {x : E}
    (hf : DifferentiableAt ℝ f x) (hA : DifferentiableAt ℝ A x) (b : Fin n) :
    strongDivergence e (fun p => fderiv ℝ (fun y => f y • A y) x (d p)) b =
      f x • strongDivergence e (fun p => fderiv ℝ A x (d p)) b +
        columnContraction e (fun p => fderiv ℝ f x (d p)) (A x) b := by
  have he (p : Fin n × Fin s) :
      fderiv ℝ (fun y => f y • A y) x (d p) =
        f x • fderiv ℝ A x (d p) + fderiv ℝ f x (d p) • A x := by
    have h := (hf.hasFDerivAt.smul hA.hasFDerivAt).fderiv
    simpa only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply]
      using! congrArg (fun L => L (d p)) h
  simp only [strongDivergence, columnContraction, he, Matrix.add_apply, Matrix.smul_apply,
    mul_add, mul_smul_comm, Finset.sum_add_distrib, Finset.smul_sum]

theorem strongDivergence_cutoff_of_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n s : ℕ} (e : Fin s → Q) (d : Fin n × Fin s → E)
    {A : E → Matrix (Fin n) (Fin n) Q} {φ : E → ℝ} {χ : ℝ → ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hφ : DifferentiableAt ℝ φ x)
    (hχ : DifferentiableAt ℝ χ (φ x))
    (hd : ∀ b, strongDivergence e (fun p => fderiv ℝ A x (d p)) b = 0)
    (ht : ∀ b, columnContraction e (fun p => fderiv ℝ φ x (d p)) (A x) b = 0) :
    ∀ b, strongDivergence e (fun p => fderiv ℝ (fun y => χ (φ y) • A y) x (d p)) b = 0 := by
  intro b
  have hc := hχ.hasDerivAt.comp_hasFDerivAt x hφ.hasFDerivAt
  have he (p : Fin n × Fin s) :
      fderiv ℝ (fun y => χ (φ y)) x (d p) = deriv χ (φ x)*fderiv ℝ φ x (d p) := by
    exact congrArg (fun L => L (d p)) hc.fderiv
  have hF : DifferentiableAt ℝ (fun y => χ (φ y)) x := hc.differentiableAt
  have hprod := strongDivergence_smul e d hF hA b
  refine hprod.trans ?_
  rw [hd, smul_zero, zero_add]
  simp only [columnContraction, he, mul_smul, ← Finset.smul_sum]
  change deriv χ (φ x) • columnContraction e (fun p => fderiv ℝ φ x (d p)) (A x) b = 0
  rw [ht, smul_zero]

theorem strongDivergence_cutoff_rankOne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n s : ℕ} (e : Fin s → Q) (d : Fin n × Fin s → E)
    {A : E → Matrix (Fin n) (Fin n) Q} {φ : E → ℝ} {χ : ℝ → ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hφ : DifferentiableAt ℝ φ x)
    (hχ : DifferentiableAt ℝ χ (φ x))
    (hd : ∀ b, strongDivergence e (fun p => fderiv ℝ A x (d p)) b = 0)
    (f : ℝ) (B : Fin n → Q) (hAB : A x = f • outer B)
    (ht : ∑ a, star (B a)*gradientMap e (fun p => fderiv ℝ φ x (d p)) a = 0) :
    ∀ b, strongDivergence e (fun p => fderiv ℝ (fun y => χ (φ y) • A y) x (d p)) b = 0 := by
  apply strongDivergence_cutoff_of_tangent e d hA hφ hχ hd
  intro b
  rw [hAB, columnContraction_smul, columnContraction_outer, ht, star_zero, zero_mul, smul_zero]

theorem realColumnConservationOn_of_strong_at {m : ℕ} {D : Set (ThinCurrentSpace m)}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) Q}
    (hA : ∀ y ∈ D, DifferentiableAt ℝ A y)
    (hd : ∀ y ∈ D, ∀ j,
      strongDivergence threeSlots (fun p => fderiv ℝ A y (currentDirection p)) j = 0) :
    RealColumnConservationOn D A := by
  intro y hy q
  simp_rw [fderiv_realCoefficient threeSlots _ _ (hA y hy)]
  exact realCoefficients_divergence_zero threeSlots _ (hd y hy) q

theorem realColumnConservationOn_cutoff_rankOne {m : ℕ} {D : Set (ThinCurrentSpace m)}
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) Q}
    {φ f : ThinCurrentSpace m → ℝ} {χ : ℝ → ℝ}
    (B : ThinCurrentSpace m → Fin (m+1) → Q)
    (hA : ∀ y ∈ D, DifferentiableAt ℝ A y)
    (hφ : ∀ y ∈ D, DifferentiableAt ℝ φ y)
    (hχ : ∀ y ∈ D, DifferentiableAt ℝ χ (φ y))
    (hd : ∀ y ∈ D, ∀ j,
      strongDivergence threeSlots (fun p => fderiv ℝ A y (currentDirection p)) j = 0)
    (hAB : ∀ y ∈ D, A y = f y • outer (B y))
    (ht : ∀ y ∈ D,
      ∑ j, star (B y j)*gradientMap threeSlots (fun p => fderiv ℝ φ y (currentDirection p)) j = 0) :
    RealColumnConservationOn D (fun y => χ (φ y) • A y) := by
  apply realColumnConservationOn_of_strong_at
  · exact fun y hy => ((hχ y hy).comp y (hφ y hy)).smul (hA y hy)
  · intro y hy
    exact strongDivergence_cutoff_rankOne threeSlots currentDirection
      (hA y hy) (hφ y hy) (hχ y hy) (hd y hy) (f y) (B y) (hAB y hy) (ht y hy)

end KakeyaSharp.Packet
