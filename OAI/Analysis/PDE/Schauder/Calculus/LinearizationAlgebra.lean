/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import OAI.Analysis.PDE.Schauder.Calculus.SliceDerivative

@[expose] public section

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {X Y Z W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fderiv_affine_factorization
    (M : Z →L[ℝ] Y) (L : X →L[ℝ] Y) (pin : X →L[ℝ] Z)
    (F : Y → W) (G : Z → W) (a : Y) (x : X) (g : Z)
    (hML : M.comp pin = L) (hbase : a+L x = M g)
    (hG : fderiv ℝ G g = (fderiv ℝ F (M g)).comp M) :
    (fderiv ℝ F (a+L x)).comp L = (fderiv ℝ G g).comp pin := by
  rw [hbase,hG,ContinuousLinearMap.comp_assoc,hML]

end OAI.Analysis.PDE.Schauder
