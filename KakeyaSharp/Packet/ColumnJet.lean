/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.ColumnDerivative

@[expose] public section

/-! A six-coordinate formula for the actual packet derivative. The two
slopes are tau/D and (r+s)/D; there are no assumed transport equations. -/
noncomputable section
namespace KakeyaSharp.Packet
open KakeyaSharp.QuaternionAlgebra

def entryJet (s u v α β c d p q dt dy₀ dy₁ dx dp₀ dp₁ : ℝ) : Q :=
  let sr := u*dy₀+v*dy₁
  let sa := -v*dy₀+u*dy₁
  let pr := u*dp₀+v*dp₁
  let pi := -v*dp₀+u*dp₁
  columnVariation u v d ((dy₀-u*sr)/s) ((dy₁-v*sr)/s)
    ((pr-α*sr+β*sa)/s) ((pi-β*sr-α*sa)/s)
    (p*dx+q*pr+(q*d-p*c)*dt-(q*c+p*d)*sr+q*β*sa)
    (q*dx-p*pr-(q*c+p*d)*dt+(p*c-q*d)*sr-p*β*sa)

theorem columnRate_eq_entryJet {m : ℕ} {r : ℝ} (a v : Fin m → ℝ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) (z : ThinCurrentSpace m) (j : Fin m) :
    columnRate r a v y z j =
      entryJet (radius y) (y.1 1/radius y) (y.1 2/radius y)
        (ratioRe y j) (ratioIm y j) (centers r a v y j) (residuals r a v y j)
        (time y/denominator r (radius y) (time y))
        ((r+radius y)/denominator r (radius y) (time y))
        (z.1 0) (z.1 1) (z.1 2) (z.2.1 j) (z.2.2 (j,0)) (z.2.2 (j,1)) := by
  have hs := hy.ne'
  ext <;> dsimp [columnRate, entryJet, columnVariation, realRate, imaginaryRate,
    centerRate, residualRate, radialRate, angularRate] <;> field_simp <;> ring

def timeJet (s u v α β c d p q : ℝ) (a : Fin 3) : Q :=
  ![entryJet s u v α β c d p q 1 0 0 0 0 0,
    entryJet s u v α β c d p q 0 1 0 0 0 0,
    entryJet s u v α β c d p q 0 0 1 0 0 0] a

def spaceJet (s u v α β c d p q : ℝ) (a : Fin 3) : Q :=
  ![entryJet s u v α β c d p q 0 0 0 1 0 0,
    entryJet s u v α β c d p q 0 0 0 0 1 0,
    entryJet s u v α β c d p q 0 0 0 0 0 1] a

theorem entryJet_zero (s u v α β c d p q : ℝ) :
    entryJet s u v α β c d p q 0 0 0 0 0 0 = 0 := by
  ext <;> simp [entryJet, columnVariation]

theorem spaceJet_divergence {s u v : ℝ} (hs : s ≠ 0) (huv : u^2+v^2=1)
    (α β c d p q : ℝ) :
    (∑ a, star (threeSlots a)*spaceJet s u v α β c d p q a) =
      (p : Q)-(q+1/s) • orientedI u v := by
  ext <;> simp [Fin.sum_univ_three, threeSlots, spaceJet, entryJet, columnVariation, orientedI]
  · field_simp
    linear_combination p*huv
  · field_simp
    ring
  · field_simp
    ring
  · ring

theorem entryJet_acceleration {s u v : ℝ} (hs : s ≠ 0) (huv : u^2+v^2=1)
    (α β c d p q : ℝ) :
    (∑ a, star (threeSlots a)*star (timeJet s u v α β c d p q a))+
      (∑ a, star (threeSlots a)*columnEntry u v α β c d*
        star (spaceJet s u v α β c d p q a)) = 0 := by
  have hv2 : v^2 = 1-u^2 := by linarith
  have hv3 : v^3 = v*(1-u^2) := by rw [pow_succ, hv2]; ring
  ext <;> simp [Fin.sum_univ_three, threeSlots, timeJet, spaceJet, entryJet,
    columnVariation, columnEntry] <;> field_simp <;> ring_nf <;>
    simp only [hv2, hv3] <;> ring

def columnTimeRate {m : ℕ} (r : ℝ) (a v : Fin m → ℝ)
    (y : ThinCurrentSpace m) (j : Fin m) (b : Fin 3) : Q :=
  timeJet (radius y) (y.1 1/radius y) (y.1 2/radius y)
    (ratioRe y j) (ratioIm y j) (centers r a v y j) (residuals r a v y j)
    (time y/denominator r (radius y) (time y))
    ((r+radius y)/denominator r (radius y) (time y)) b

def columnSpaceRate {m : ℕ} (r : ℝ) (a v : Fin m → ℝ)
    (y : ThinCurrentSpace m) (j : Fin m) (b : Fin 3) : Q :=
  spaceJet (radius y) (y.1 1/radius y) (y.1 2/radius y)
    (ratioRe y j) (ratioIm y j) (centers r a v y j) (residuals r a v y j)
    (time y/denominator r (radius y) (time y))
    ((r+radius y)/denominator r (radius y) (time y)) b

theorem physicalColumn_parameter_fderiv {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y) (j : Fin m) (b : Fin 3) :
    fderiv ℝ (fun w => physicalColumn r a v w j.succ) y (parameterDirection b) =
      columnTimeRate r a v y j b := by
  rw [physicalColumn_fderiv hr a v hy, columnRate_eq_entryJet a v hy]
  fin_cases b <;> simp [parameterDirection, columnTimeRate, timeJet]

theorem physicalColumn_spatial_fderiv {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y)
    (i j : Fin m) (b : Fin 3) :
    fderiv ℝ (fun w => physicalColumn r a v w j.succ) y (spatialDirection (i,b)) =
      if i=j then columnSpaceRate r a v y j b else 0 := by
  classical
  rw [physicalColumn_fderiv hr a v hy, columnRate_eq_entryJet a v hy]
  by_cases hij : i=j
  · subst i
    fin_cases b <;> simp [spatialDirection, thinDirection, columnSpaceRate, spaceJet]
  · fin_cases b <;> simp [spatialDirection, thinDirection, hij, Ne.symm hij, entryJet_zero]

theorem physicalColumn_zero_fderiv {m : ℕ} (r : ℝ) (a v : Fin m → ℝ)
    (y z : ThinCurrentSpace m) : fderiv ℝ (fun w => physicalColumn r a v w 0) y z = 0 := by
  simp only [physicalColumn_zero, fderiv_const_apply, _root_.zero_apply]

theorem physicalColumn_spatial_divergence {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y) (j : Fin m) :
    (∑ b, star (threeSlots b)*
      fderiv ℝ (fun w => physicalColumn r a v w j.succ) y (spatialDirection (j,b))) =
      (time y/denominator r (radius y) (time y) : ℝ)-
        ((r+radius y)/denominator r (radius y) (time y)+1/radius y) •
          orientedI (y.1 1/radius y) (y.1 2/radius y) := by
  simp only [physicalColumn_spatial_fderiv hr a v hy, ite_true, columnSpaceRate]
  exact spaceJet_divergence hy.ne' (physicalFrame_unit hy) _ _ _ _ _ _

theorem physicalColumn_acceleration {m : ℕ} {r : ℝ} (hr : 0 < r)
    (a v : Fin m → ℝ) {y : ThinCurrentSpace m} (hy : 0 < radius y) (j : Fin (m+1)) :
    (∑ i, ∑ b, star (threeSlots b)*physicalColumn r a v y i*
      star (fderiv ℝ (fun w => physicalColumn r a v w j) y (currentDirection (i,b)))) = 0 := by
  classical
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [physicalColumn_zero_fderiv, star_zero, mul_zero, Finset.sum_const_zero]
  · rw [Fin.sum_univ_succ]
    simp only [currentDirection, Fin.cases_zero, Fin.cases_succ,
      physicalColumn_zero, mul_one, physicalColumn_parameter_fderiv hr a v hy,
      physicalColumn_spatial_fderiv hr a v hy, apply_ite star, star_zero, mul_ite, mul_zero]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact entryJet_acceleration hy.ne' (physicalFrame_unit hy) _ _ _ _ _ _

end KakeyaSharp.Packet
