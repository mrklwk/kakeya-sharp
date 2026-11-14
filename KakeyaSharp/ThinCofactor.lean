/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinDomain
public import KakeyaSharp.Green.EnergyIdentities

@[expose] public section

/-! The actual cofactor field for the three-slot Hessian and its Green identities. -/
noncomputable section
namespace KakeyaSharp
open Matrix Set MeasureTheory KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped ContDiff Matrix.Norms.Elementwise

def thinCofactor {m : ℕ} (f : ThinSpace m → ℝ) (z : ThinSpace m) :
    Matrix (Fin m) (Fin m) (Quaternion ℝ) :=
  mooreCofactor m (thinQuaternionHessian f z)

theorem thinQuaternionHessian_isHermitian {m : ℕ}
    {f : ThinSpace m → ℝ} {z : ThinSpace m} (hf : ContDiffAt ℝ 2 f z) :
    (thinQuaternionHessian f z).IsHermitian :=
  Green.directionalHessian_isHermitian threeSlots (fun p => thinDirection p.1 p.2) hf

theorem thinCofactor_divergence {m : ℕ} {f : ThinSpace m → ℝ}
    {z : ThinSpace m} (hf : ContDiffAt ℝ 3 f z) (b : Fin m) :
    strongDivergence threeSlots
      (fun p => fderiv ℝ (thinCofactor f) z (thinDirection p.1 p.2)) b = 0 :=
  mooreCofactor_directionalHessian_divergence threeSlots
    (fun p => thinDirection p.1 p.2) hf b

theorem thinCofactor_euler {m : ℕ} {f : ThinSpace m → ℝ}
    {z : ThinSpace m} (hf : ContDiffAt ℝ 2 f z) :
    realTrace (thinCofactor f z * thinQuaternionHessian f z) =
      (m : ℝ) * mooreDet m (thinQuaternionHessian f z) :=
  mooreCofactor_euler _ (thinQuaternionHessian_isHermitian hf)

theorem thinCofactor_selfAdjoint {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {ψ u v : ThinSpace m → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hzu : ∀ z, ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 = R ^ 2 → u z = 0)
    (hzv : ∀ z, ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 = R ^ 2 → v z = 0) :
    (∫ z in thinBallAt R o, u z * mooreDifferential m (thinQuaternionHessian ψ z)
        (thinQuaternionHessian v z)) =
    ∫ z in thinBallAt R o, v z * mooreDifferential m (thinQuaternionHessian ψ z)
        (thinQuaternionHessian u z) := by
  let : (volume : Measure (ThinSpace m)).IsAddHaarMeasure := by
    change ((volume : Measure (Space m)).prod (volume : Measure (ThinTransverseSpace m))).IsAddHaarMeasure
    infer_instance
  exact Green.moore_cofactor_selfAdjoint_bounded threeSlots
    (fun p => thinDirection p.1 p.2) (thinBallAt_isOpen R o)
    (thinBallAt_bounded hR.le o) (thinBallAt_null_frontier R o) hψ hu hv
    (fun z hz => hzu z (thinBallAt_frontier_subset R o hz))
    (fun z hz => hzv z (thinBallAt_frontier_subset R o hz))

theorem thinEnergy_linearization {m : ℕ} {R : ℝ} (hR : 0 < R) (o : ThinSpace m)
    {u v : ThinSpace m → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 2 v)
    (hzu : ∀ z, ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 = R ^ 2 → u z = 0)
    (hzv : ∀ z, ‖z.1 - o.1‖ ^ 2 + ‖z.2 - o.2‖ ^ 2 = R ^ 2 → v z = 0) :
    (∫ z in thinBallAt R o, u z * mooreDifferential m (thinQuaternionHessian u z)
        (thinQuaternionHessian v z)) =
      (m : ℝ) * ∫ z in thinBallAt R o, v z * mooreDet m (thinQuaternionHessian u z) := by
  let : (volume : Measure (ThinSpace m)).IsAddHaarMeasure := by
    change ((volume : Measure (Space m)).prod (volume : Measure (ThinTransverseSpace m))).IsAddHaarMeasure
    infer_instance
  exact Green.moore_energy_linearization_bounded threeSlots
    (fun p => thinDirection p.1 p.2) (thinBallAt_isOpen R o)
    (thinBallAt_bounded hR.le o) (thinBallAt_null_frontier R o) hu hv
    (fun z hz => hzu z (thinBallAt_frontier_subset R o hz))
    (fun z hz => hzv z (thinBallAt_frontier_subset R o hz))

end KakeyaSharp

