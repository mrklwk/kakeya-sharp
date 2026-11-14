/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.Physical

@[expose] public section

/-! Volume-preserving real coordinates for the three spatial slots. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace KakeyaSharp.Packet
open MeasureTheory

abbrev PacketCoordinates (m : ℕ) := Fin 3 × Fin m → ℝ

def packetIndexEquiv (m : ℕ) : Fin 3 × Fin m ≃ Fin m ⊕ (Fin m × Fin 2) where
  toFun p := Fin.cases (Sum.inl p.2) (fun a => Sum.inr (p.2,a)) p.1
  invFun p := p.elim (fun j => (0,j)) (fun q => (q.2.succ,q.1))
  left_inv p := by
    rcases p with ⟨a,j⟩
    fin_cases a <;> rfl
  right_inv p := by
    rcases p with j | ⟨j,a⟩
    · rfl
    · fin_cases a <;> rfl

def unpackLinear (m : ℕ) : PacketCoordinates m ≃ₗ[ℝ] ThinSpace m where
  toFun z := (WithLp.toLp 2 (fun j => z (0,j)),
    WithLp.toLp 2 (fun p => z (p.2.succ,p.1)))
  invFun z := fun p => Fin.cases (z.1 p.2) (fun a => z.2 (p.2,a)) p.1
  left_inv z := by
    funext ⟨a,j⟩
    fin_cases a <;> rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · ext ⟨j,a⟩
      fin_cases a <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def unpack (m : ℕ) : PacketCoordinates m ≃L[ℝ] ThinSpace m :=
  (unpackLinear m).toContinuousLinearEquiv

theorem unpack_measurePreserving (m : ℕ) : MeasurePreserving (unpack m) volume volume := by
  have h := ((PiLp.volume_preserving_toLp (Fin m)).prod
    (PiLp.volume_preserving_toLp (Fin m × Fin 2))).comp
    ((volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin m ⊕ (Fin m × Fin 2) => ℝ)).comp
      (volume_measurePreserving_piCongrLeft
        (fun _ : Fin m ⊕ (Fin m × Fin 2) => ℝ) (packetIndexEquiv m)))
  convert h using 1
  rfl

theorem integral_unpack (m : ℕ) (f : ThinSpace m → ℝ) :
    (∫ z : PacketCoordinates m, f (unpack m z)) = ∫ z, f z :=
  (unpack_measurePreserving m).integral_comp (unpack m).toHomeomorph.measurableEmbedding f

end KakeyaSharp.Packet
