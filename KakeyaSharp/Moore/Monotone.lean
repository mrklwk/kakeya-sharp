/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Moore.Positive

@[expose] public section

/-! Strict ellipticity and determinant monotonicity on the positive cone. -/

noncomputable section

namespace KakeyaSharp.Moore

open Matrix Set
open scoped MatrixOrder ComplexOrder

theorem mooreDifferential_nonneg_of_posDef {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify D).PosSemidef) :
    0 ≤ mooreDifferential n A D := by
  obtain ⟨C, hAC, hCA⟩ := exists_quaternion_inverse_of_complexify_posDef A hA
  exact mooreDifferential_nonneg n A D C hA hD hAC hCA
    (mooreDet_pos_of_complexify_posDef A hA).le


end KakeyaSharp.Moore

