/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.GraphTubeGeometry

@[expose] public section

/-! Finitely many orthogonal direction charts, constructed from a sphere
net and reflections. Rotations preserve actual tubes, volume and separation. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open Set Metric MeasureTheory

def chartRotation {m : ℕ} (b : Space (m+1)) : Space (m+1) ≃ₗᵢ[ℝ] Space (m+1) :=
  (ℝ ∙ (b-north m))ᗮ.reflection

theorem chartRotation_center {m : ℕ} {b : Space (m+1)} (hb : ‖b‖=1) :
    chartRotation b b=north m :=
  Submodule.reflection_sub (by rw [hb,norm_north])

theorem exists_finite_direction_charts (m : ℕ) :
    ∃ (J : ℕ) (R : Fin J → Space (m+1) ≃ₗᵢ[ℝ] Space (m+1)),
      ∀ v : Space (m+1), ‖v‖=1 → ∃ j, dist (R j v) (north m) ≤ 1/16 := by
  obtain ⟨J,b,hb,_,hcover⟩ := unit_sphere_finite_separated_net
    (n := m+1) (by norm_num : (0 : ℝ) < 1/16)
  refine ⟨J,fun j => chartRotation (b j),?_⟩
  intro v hv
  obtain ⟨j,hj⟩ := hcover v hv
  refine ⟨j,?_⟩
  rw [← chartRotation_center (hb j),LinearIsometryEquiv.dist_map]
  exact hj

theorem rotated_tube_preimage {n : ℕ} (R : Space n ≃ₗᵢ[ℝ] Space n)
    (r : ℝ) (v c : Space n) :
    R ⁻¹' tube r (R v) (R c)=tube r v c := by
  ext y
  simp only [mem_preimage,mem_tube_iff]
  apply exists_congr
  intro t
  rw [← R.map_smul t v,← R.map_add c (t • v),R.dist_map]

theorem integral_rotation {n : ℕ} (R : Space n ≃ₗᵢ[ℝ] Space n) (f : Space n → ℝ) :
    (∫ y, f (R y))=∫ y, f y :=
  R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding f

theorem rotation_preserves_separation {n N : ℕ} (R : Space n ≃ₗᵢ[ℝ] Space n)
    {δ : ℝ} (v : Fin N → Space n)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) :
    ∀ i j, i ≠ j → δ ≤ dist (R (v i)) (R (v j)) := by
  intro i j hij
  simpa only [R.dist_map] using hsep i j hij

end KakeyaSharp.Graph
