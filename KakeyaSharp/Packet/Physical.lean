/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.FinitePhase
public import KakeyaSharp.Packet.Prefactor
public import KakeyaSharp.ThinCurrentRegularization

@[expose] public section

/-! The packet formulas on the actual parameter and spatial coordinates.
The mass-normalizing constant is not included in `rawPacket`. -/
noncomputable section
namespace KakeyaSharp.Packet
open Matrix KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore
open scoped Matrix.Norms.Elementwise

def radius {m : ℕ} (y : ThinCurrentSpace m) : ℝ := Real.sqrt ((y.1 1)^2+(y.1 2)^2)
def time {m : ℕ} (y : ThinCurrentSpace m) : ℝ := y.1 0-1

def ratioRe {m : ℕ} (y : ThinCurrentSpace m) (j : Fin m) : ℝ :=
  (y.1 1*y.2.2 (j,0)+y.1 2*y.2.2 (j,1))/((y.1 1)^2+(y.1 2)^2)

def ratioIm {m : ℕ} (y : ThinCurrentSpace m) (j : Fin m) : ℝ :=
  (y.1 1*y.2.2 (j,1)-y.1 2*y.2.2 (j,0))/((y.1 1)^2+(y.1 2)^2)

def centers {m : ℕ} (r : ℝ) (a v : Fin m → ℝ) (y : ThinCurrentSpace m) (j : Fin m) : ℝ :=
  center r (radius y) (time y) (a j) (v j) (y.2.1 j) (ratioRe y j)

def residuals {m : ℕ} (r : ℝ) (a v : Fin m → ℝ) (y : ThinCurrentSpace m) (j : Fin m) : ℝ :=
  residual r (radius y) (time y) (a j) (v j) (y.2.1 j) (ratioRe y j)

def physicalPhase {m : ℕ} (r : ℝ) (a v : Fin m → ℝ) (y : ThinCurrentSpace m) : ℝ :=
  phase r (radius y) (time y) a v (fun j => y.2.1 j) (ratioRe y) (ratioIm y)

def physicalColumn {m : ℕ} (r : ℝ) (a v : Fin m → ℝ) (y : ThinCurrentSpace m) : Fin (m+1) → Q :=
  column (y.1 1/radius y) (y.1 2/radius y) (ratioRe y) (ratioIm y) (centers r a v y) (residuals r a v y)

def packetWeight {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (χ : ℝ → ℝ) (y : ThinCurrentSpace m) : ℝ :=
  prefactor m r (radius y) (time y)*χ (physicalPhase r a v y/h)

def rawPacket {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (χ : ℝ → ℝ)
    (y : ThinCurrentSpace m) : Matrix (Fin (m+1)) (Fin (m+1)) Q :=
  packetWeight r h a v χ y • outer (physicalColumn r a v y)

theorem radius_sq {m : ℕ} (y : ThinCurrentSpace m) :
    (radius y)^2=(y.1 1)^2+(y.1 2)^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem physicalFrame_unit {m : ℕ} {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    (y.1 1/radius y)^2+(y.1 2/radius y)^2=1 := by
  field_simp
  exact (radius_sq y).symm

theorem physicalPhase_nonneg {m : ℕ} {r : ℝ} (hr : 0 < r) (a v : Fin m → ℝ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) : 0 ≤ physicalPhase r a v y :=
  phase_nonneg hr hy _ _ _ _ _ _

theorem physicalColumn_zero {m : ℕ} (r : ℝ) (a v : Fin m → ℝ) (y : ThinCurrentSpace m) :
    physicalColumn r a v y 0 = 1 := rfl

theorem rawPacket_isHermitian {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (χ : ℝ → ℝ)
    (y : ThinCurrentSpace m) : (rawPacket r h a v χ y).IsHermitian := by
  rw [rawPacket, Matrix.IsHermitian, quaternionMatrix_conjTranspose_real_smul,
    (outer_isHermitian _).eq]

theorem rawPacket_density {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (χ : ℝ → ℝ)
    (y : ThinCurrentSpace m) : currentDensity (rawPacket r h a v χ) y = packetWeight r h a v χ y := by
  simp [currentDensity, rawPacket, outer, physicalColumn_zero]

theorem rawPacket_flux {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (χ : ℝ → ℝ)
    (y : ThinCurrentSpace m) :
    currentFlux (rawPacket r h a v χ) y =
      packetWeight r h a v χ y • (fun j => physicalColumn r a v y j.succ) := by
  funext j
  simp [currentFlux, rawPacket, outer, physicalColumn_zero]

theorem rawPacket_stress {m : ℕ} (r h : ℝ) (a v : Fin m → ℝ) (χ : ℝ → ℝ)
    (y : ThinCurrentSpace m) :
    currentStress (rawPacket r h a v χ) y =
      packetWeight r h a v χ y • outer (fun j => physicalColumn r a v y j.succ) := by
  rfl

theorem rawPacket_density_nonneg {m : ℕ} {r : ℝ} (hr : 0 < r) (h : ℝ)
    (a v : Fin m → ℝ) {χ : ℝ → ℝ} (hχ : ∀ x, 0 ≤ χ x)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) : 0 ≤ currentDensity (rawPacket r h a v χ) y := by
  rw [rawPacket_density]
  exact mul_nonneg (prefactor_pos m hr hy _).le (hχ _)

theorem physicalColumn_tangency_formula {m : ℕ} (r : ℝ) (a v : Fin m → ℝ)
    {y : ThinCurrentSpace m} (hy : 0 < radius y) :
    (∑ j, star (physicalColumn r a v y j)*
      phaseGradient (y.1 1/radius y) (y.1 2/radius y)
        (ratioRe y) (ratioIm y) (centers r a v y) (residuals r a v y) j) = 0 :=
  column_phaseGradient_tangency (physicalFrame_unit hy) _ _ _ _

end KakeyaSharp.Packet
