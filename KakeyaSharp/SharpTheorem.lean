/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.AllDirectionTubes

@[expose] public section

/-! Unconditional sharp-logarithm Kakeya upper bounds in dimensions at least
two, for the actual normalized Euclidean tube maximal operator. -/
noncomputable section
namespace KakeyaSharp
open MeasureTheory

/-- The weighted Euclidean overlap estimate with one logarithm. -/
theorem sharpTubeBound_of_two_le {n : ℕ} (hn : 2 ≤ n) : SharpTubeBound n := by
  rcases n with _ | m
  · omega
  have hm : 1 ≤ m := by omega
  obtain ⟨C,hC,hbound⟩ := Graph.exists_allDirectionTube_constant hm
  refine ⟨C,hC,?_⟩
  intro N δ hδ hδ1 v c hv hsep weights hw
  have h := hbound N δ hδ hδ1 v c weights hw hv hsep
  simpa only [Graph.weightedTubeOverlap,Packet.inputExponent,overlapExponent,
    Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one,Nat.add_sub_cancel,
    add_sub_cancel_right] using h

/-- The full supremum over spatial centers, with actual tube-volume
normalization and the factor log(2/delta)^((n-1)/n). -/
theorem sharpMaximalBound_of_two_le {n : ℕ} (hn : 2 ≤ n) : SharpMaximalBound n :=
  sharpMaximal_of_sharpTube (by omega) (sharpTubeBound_of_two_le hn)

/-- Compatibility with the preceding checkpoint. -/
theorem sharpTubeBound_of_three_le {n : ℕ} (hn : 3 ≤ n) : SharpTubeBound n :=
  sharpTubeBound_of_two_le (by omega)

theorem sharpMaximalBound_of_three_le {n : ℕ} (hn : 3 ≤ n) : SharpMaximalBound n :=
  sharpMaximalBound_of_two_le (by omega)

end KakeyaSharp
