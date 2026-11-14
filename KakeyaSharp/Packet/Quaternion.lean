/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.QuaternionAlgebra

@[expose] public section

/-! Quaternionic packet identities at every orientation of the parameter Y.
The normalized coordinates u,v satisfy u²+v²=1. -/
noncomputable section
namespace KakeyaSharp.Packet
open KakeyaSharp.QuaternionAlgebra

def orientedI (u v : ℝ) : Q := ⟨0,u,v,0⟩
def orientedJ (u v : ℝ) : Q := ⟨0,-v,u,0⟩
def unitK : Q := ⟨0,0,0,1⟩

def columnEntry (u v α β c d : ℝ) : Q := ⟨(α+c)/2,-u*d/2,-v*d/2,β/2⟩

def spatialPhaseGradient (u v α β c d : ℝ) : Q :=
  ⟨2*d,2*(u*(α-c)-v*β),2*(v*(α-c)+u*β),0⟩

def parameterPhaseGradient (u v α β c d : ℝ) : Q :=
  ⟨-2*c*d,u*(c^2-d^2-α^2-β^2)+2*v*c*β,
    v*(c^2-d^2-α^2-β^2)-2*u*c*β,0⟩

theorem column_phase_tangency {u v : ℝ} (h : u^2+v^2=1) (α β c d : ℝ) :
    parameterPhaseGradient u v α β c d +
      star (columnEntry u v α β c d)*spatialPhaseGradient u v α β c d = 0 := by
  ext <;> simp [parameterPhaseGradient, columnEntry, spatialPhaseGradient]
  · linear_combination -d*(α-c)*h
  · ring
  · ring
  · linear_combination d*β*h

theorem column_sandwich {u v : ℝ} (h : u^2+v^2=1) (α β c d : ℝ) :
    columnEntry u v α β c d + orientedI u v*columnEntry u v α β c d*orientedI u v =
      β • unitK := by
  ext <;> simp [columnEntry, orientedI, unitK]
  · linear_combination -(α+c)/2*h
  · linear_combination u*d/2*h
  · linear_combination v*d/2*h
  · linear_combination β/2*h

theorem column_commutator (u v α β c d : ℝ) :
    columnEntry u v α β c d*orientedI u v - orientedI u v*columnEntry u v α β c d =
      β • orientedJ u v := by
  ext <;> simp [columnEntry, orientedI, orientedJ] <;> ring

theorem column_mixed_product {u v : ℝ} (h : u^2+v^2=1) (α β c d : ℝ) :
    orientedJ u v*columnEntry u v α β c d*unitK - orientedI u v*columnEntry u v α β c d =
      (-d : ℝ) := by
  ext <;> simp [columnEntry, orientedI, orientedJ, unitK]
  · linear_combination -d*h
  · ring
  · ring

end KakeyaSharp.Packet
