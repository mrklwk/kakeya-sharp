/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.VariationalRepresentation
public import KakeyaSharp.Calculus.Maximum

@[expose] public section

/-! A quadratic barrier and the maximum principle for admissible functions. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff

def thinQuadraticAt {m : ℕ} (R : ℝ) (o z : ThinSpace m) : ℝ :=
  projectedQuadratic (ContinuousLinearMap.fst ℝ (Space m) (ThinTransverseSpace m))
    (-R^2/6) (1/6) (z-o) +
  projectedQuadratic (ContinuousLinearMap.snd ℝ (Space m) (ThinTransverseSpace m))
    0 (1/6) (z-o)

theorem thinQuadraticAt_apply {m : ℕ} (R : ℝ) (o z : ThinSpace m) :
    thinQuadraticAt R o z = (‖z.1-o.1‖^2+‖z.2-o.2‖^2-R^2)/6 := by
  change (-R^2/6 + (1/6)*‖z.1-o.1‖^2) + (0+(1/6)*‖z.2-o.2‖^2) = _
  ring

theorem thinQuadraticAt_smooth {m : ℕ} (R : ℝ) (o : ThinSpace m) :
    ContDiff ℝ ∞ (thinQuadraticAt R o) :=
  ((projectedQuadratic_smooth _ _ _).add (projectedQuadratic_smooth _ _ _)).comp
    (contDiff_id.sub contDiff_const)

theorem thinQuadraticAt_hessian {m : ℕ} (R : ℝ) (o z : ThinSpace m) :
    thinQuaternionHessian (thinQuadraticAt R o) z =
      (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) := by
  change thinQuaternionHessian (fun y => ((projectedQuadratic
    (ContinuousLinearMap.fst ℝ (Space m) (ThinTransverseSpace m)) (-R^2/6) (1/6)) +
    projectedQuadratic (ContinuousLinearMap.snd ℝ (Space m) (ThinTransverseSpace m)) 0 (1/6)) (y-o)) z = _
  rw [thinQuaternionHessian_comp_sub,
    thinQuaternionHessian_add ((projectedQuadratic_smooth _ _ _).of_le (by norm_num))
      ((projectedQuadratic_smooth _ _ _).of_le (by norm_num))]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, thinQuaternionHessian, hessianMap, thinRealHessian,
    hessian_projectedQuadratic, Fin.sum_univ_three]
  by_cases hij : i=j
  · subst j
    ext <;> simp [thinDirection, threeSlots, EuclideanSpace.inner_single_right]; ring
  · ext <;> simp [thinDirection, threeSlots, EuclideanSpace.inner_single_right, hij, Ne.symm hij]

theorem thinQuadraticAt_admissible {m : ℕ} (R : ℝ) (o : ThinSpace m) :
    ThinAdmissibleAt R o (thinQuadraticAt R o) := by
  refine ⟨fun _ _ => (thinQuadraticAt_smooth R o).contDiffAt.of_le (by simp), ?_, ?_⟩
  · intro z hz
    rw [thinQuadraticAt_apply, hz, sub_self, zero_div]
  · intro z _ w
    rw [thinQuadraticAt_hessian, quaternionForm_one]
    exact quaternionSize_nonneg w

theorem quaternionForm_single {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (i : Fin m) :
    quaternionForm A (Pi.single i 1) = (A i i).re := by
  simp [quaternionForm, Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite star]

theorem thinTrace_eq {m : ℕ} (f : ThinSpace m → ℝ) (z : ThinSpace m) :
    Maximum.ellipticValue (fun _ _ => (1 : ℝ))
      (fun (_ : ThinSpace m) (p : Fin m × Fin 3) => thinDirection p.1 p.2) f z =
      ∑ i : Fin m, (thinQuaternionHessian f z i i).re := by
  simp only [thinQuaternionHessian, hessianMap_diagonal_re threeSlots threeSlots_orthonormal]
  simp [Maximum.ellipticValue, thinRealHessian, Fintype.sum_prod_type]

theorem thinTrace_nonneg {m : ℕ} {f : ThinSpace m → ℝ} {z : ThinSpace m}
    (hpos : ∀ w, 0 ≤ quaternionForm (thinQuaternionHessian f z) w) :
    0 ≤ Maximum.ellipticValue (fun _ _ => (1 : ℝ))
      (fun (_ : ThinSpace m) (p : Fin m × Fin 3) => thinDirection p.1 p.2) f z := by
  rw [thinTrace_eq]
  apply Finset.sum_nonneg
  intro i _
  simpa only [quaternionForm_single] using hpos (Pi.single i 1)

theorem thinQuadraticAt_trace {m : ℕ} (R : ℝ) (o z : ThinSpace m) :
    Maximum.ellipticValue (fun _ _ => (1 : ℝ))
      (fun (_ : ThinSpace m) (p : Fin m × Fin 3) => thinDirection p.1 p.2) (thinQuadraticAt R o) z = m := by
  rw [thinTrace_eq, thinQuadraticAt_hessian]
  simp

theorem ThinAdmissibleAt.nonpos {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    {o : ThinSpace m} {f : ThinSpace m → ℝ} (hf : ThinAdmissibleAt R o f) :
    ∀ z ∈ thinClosedBallAt R o, f z ≤ 0 := by
  obtain ⟨g,hg,-,-,hgf⟩ := hf.exists_C3_representative hR
  have hL : ∀ z ∈ interior (thinClosedBallAt R o),
      0 ≤ Maximum.ellipticValue (fun _ _ => (1 : ℝ))
        (fun (_ : ThinSpace m) (p : Fin m × Fin 3) => thinDirection p.1 p.2) g z := by
    intro z hz
    apply thinTrace_nonneg
    intro w
    rw [thinQuaternionHessian_congr_nhds (hgf z (interior_subset hz))]
    exact hf.2.2 z (interior_subset hz) w
  have hbd : ∀ z ∈ thinClosedBallAt R o, z ∉ interior (thinClosedBallAt R o) → g z ≤ 0 := by
    intro z hz hn
    have he : ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 := by
      apply le_antisymm hz
      by_contra hh
      have hlt : z ∈ thinBallAt R o := lt_of_not_ge hh
      have hs : thinBallAt R o ⊆ interior (thinClosedBallAt R o) :=
        (thinBallAt_isOpen R o).subset_interior_iff.mpr (fun x hx => by
          exact show ‖x.1-o.1‖^2+‖x.2-o.2‖^2 ≤ R^2 from hx.le)
      exact hn (hs hlt)
    rw [(hgf z hz).self_of_nhds, hf.2.1 z he]
  have h := Maximum.maximum_principle_of_barrier (thinClosedBallAt_compact hR.le o)
    (hg.of_le (by norm_num)) ((thinQuadraticAt_smooth R o).of_le (by norm_num))
    (fun _ _ _ => zero_le_one) hL
    (fun z _ => by
      rw [thinQuadraticAt_trace]
      exact_mod_cast (show 0 < m by omega)) hbd
  intro z hz
  rw [← (hgf z hz).self_of_nhds]
  exact h z hz

end KakeyaSharp

