/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Moore.Outer
public import KakeyaSharp.QuaternionPositive

@[expose] public section

/-! Exact signed Moore determinants of a scalar matrix plus one outer product. -/

noncomputable section
namespace KakeyaSharp.Moore
open Matrix KakeyaSharp.QuaternionAlgebra

theorem hasDerivAt_mooreDet_affine {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ) :
    HasDerivAt (fun s => mooreDet n (A + s • D))
      (mooreDifferential n (A + t • D) D) t := by
  apply hasDerivAt_mooreDet_path
  intro i j
  convert! ((hasDerivAt_id t).smul_const (D i j)).const_add (A i j) using 1
  simp

theorem mooreDifferential_outer {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v : Fin n → Quaternion ℝ) :
    mooreDifferential n A (outer v) = mooreDet n (A + outer v) - mooreDet n A := by
  have hc : HasDerivAt (fun s : ℝ => mooreDet n (A + s • outer v))
      (mooreDet n (A + outer v) - mooreDet n A) 0 := by
    simp_rw [mooreDet_add_outer]
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const
      (mooreDet n (A + outer v) - mooreDet n A)).const_add (mooreDet n A) using 1
    simp
  have hd := hasDerivAt_mooreDet_affine A (outer v) 0
  simpa only [zero_smul, add_zero] using hd.unique hc

theorem mooreDet_add_outer_differential {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v : Fin n → Quaternion ℝ) (t : ℝ) :
    mooreDet n (A + t • outer v) = mooreDet n A + t * mooreDifferential n A (outer v) := by
  rw [mooreDet_add_outer, mooreDifferential_outer]

theorem mooreDifferential_identity_outer {n : ℕ} (v : Fin n → Quaternion ℝ) :
    mooreDifferential n 1 (outer v) = quaternionSize v := by
  rw [mooreDifferential_inverse n 1 (outer v) 1 isHermitian_one
    (outer_isHermitian v) (one_mul 1) (one_mul 1), mooreDet_identity, one_mul, one_mul]
  simp [outer, Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self,
    quaternionSize, pow_two]

theorem mooreDet_identity_outer {n : ℕ} (v : Fin n → Quaternion ℝ) (t : ℝ) :
    mooreDet n (1 + t • outer v) = 1 + t * quaternionSize v := by
  rw [mooreDet_add_outer_differential, mooreDet_identity, mooreDifferential_identity_outer]

theorem mooreDet_scalar_outer {n : ℕ} (hn : 1 ≤ n) (v : Fin n → Quaternion ℝ)
    {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    mooreDet n (c • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) + t • outer v) =
      c ^ (n - 1) * (c + t * quaternionSize v) := by
  have he : c • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) + t • outer v =
      c • (1 + (t / c) • outer v) := by
    rw [smul_add, smul_smul, mul_div_cancel₀ t hc]
  rw [he, mooreDet_smul, mooreDet_identity_outer]
  have hp : c ^ n = c ^ (n - 1) * c := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hp]
  field_simp

end KakeyaSharp.Moore
