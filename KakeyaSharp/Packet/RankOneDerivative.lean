/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.CoordinateDerivative
public import KakeyaSharp.Packet.Cutoff

@[expose] public section

/-! The actual product rule for a scalar multiple of a quaternionic outer
product, with the two conservation terms separated. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp.Packet
open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped Matrix.Norms.Elementwise

theorem fderiv_smul_outer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {f : E → ℝ} {B : E → Fin n → Q} {x : E}
    (hf : DifferentiableAt ℝ f x) (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (z : E) :
    fderiv ℝ (fun y => f y • outer (B y)) x z =
      fun i j => (fderiv ℝ f x z • B x i+f x • fderiv ℝ (fun y => B y i) x z)*star (B x j)+
        f x • (B x i*star (fderiv ℝ (fun y => B y j) x z)) := by
  have hA : DifferentiableAt ℝ (fun y => f y • outer (B y)) x := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact hf.smul ((hB i).mul (quaternionStarCLM.differentiableAt.comp x (hB j)))
  apply fderiv_eq_of_line hA
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have he : x = line x z 0 := by simp [line]
  have hF := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line x z) he
  have hI := (hB i).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line x z) he
  have hJ := (hB j).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line x z) he
  have hS := quaternionStarCLM.hasFDerivAt.comp_hasDerivAt 0 hJ
  have h := (hF.smul hI).mul hS
  simp only [Pi.smul_apply', Function.comp_apply, ← he, smul_mul_assoc] at h
  refine h.congr_deriv ?_
  simp only [add_mul, smul_mul_assoc]
  dsimp [quaternionStarCLM, quaternionStarLinear]
  abel

theorem strongDivergence_smul_outer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n s : ℕ} (e : Fin s → Q) (d : Fin n × Fin s → E)
    {f : E → ℝ} {B : E → Fin n → Q} {x : E}
    (hf : DifferentiableAt ℝ f x) (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (j : Fin n) :
    strongDivergence e (fun p => fderiv ℝ (fun y => f y • outer (B y)) x (d p)) j =
      (∑ i : Fin n, ∑ a : Fin s, (fderiv ℝ f x (d (i,a)) • (star (e a)*B x i)+
        f x • (star (e a)*fderiv ℝ (fun y => B y i) x (d (i,a)))))*star (B x j)+
      f x • (∑ i : Fin n, ∑ a : Fin s, star (e a)*B x i*star (fderiv ℝ (fun y => B y j) x (d (i,a)))) := by
  simp only [strongDivergence, fderiv_smul_outer hf hB, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.smul_sum, mul_assoc]

end KakeyaSharp.Packet
