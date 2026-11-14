/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.ThinLocalCongruence

@[expose] public section

/-! Full localization of smooth scalar transfer. Only C³ solution germs and
C² current germs near the closed spatial ball are required at each parameter.
Global smooth representatives are constructed and used on a smaller open set. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace KakeyaSharp
open Matrix Set Filter MeasureTheory InnerProductSpace Laplacian
open KakeyaSharp.QuaternionAlgebra KakeyaSharp.Moore KakeyaSharp.Green
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem thinValueRealAt_current_local_regular {m N : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    {U : ThinCurrentSpace m → ℝ} (hU : ∀ p ∈ Ω, ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 3 U (p,z))
    (hadm : ∀ p ∈ Ω, ThinAdmissibleAt R o (thinSlice U p))
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ∀ p ∈ Ω, ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 2 A (p,z)) (hH : ∀ y ∈ Ω ×ˢ thinBallAt R o, (A y).IsHermitian)
    (hd : RealColumnConservationOn (Ω ×ˢ thinBallAt R o) A)
    (hEq : ∀ p ∈ Ω, ∀ z, z ∈ thinBallAt R o →
      mooreDet m (thinQuaternionHessian (thinSlice U p) z) = currentDensity A (p,z))
    (hpos : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian (thinSlice U p) z) w)
    (hzS : ∀ p ∈ Ω, ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → currentStress A (p,z) = 0)
    (ρ : ThinCurrentSpace m → Fin N → ℝ) (b : ThinCurrentSpace m → Fin N → Fin m → Quaternion ℝ)
    (hρ : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, ∀ l, 0 ≤ ρ (p,z) l)
    (hmass : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, currentDensity A (p,z) = ∑ l, ρ (p,z) l)
    (hflux : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, currentFlux A (p,z) = ∑ l, ρ (p,z) l • b (p,z) l)
    (hstress : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o,
      currentStress A (p,z) = ∑ l, ρ (p,z) l • QuaternionAlgebra.outer (b (p,z) l)) (p : Space 3) (hp : p ∈ Ω) :
    ContDiffAt ℝ 2 (fun q => thinValueRealAt R o (thinSlice (currentDensity A) q)) p ∧
      laplacian (fun q => thinValueRealAt R o (thinSlice (currentDensity A) q)) p ≤ 0 := by
  obtain ⟨V, hV, WU, hWU, hpU, hUΩ, heU⟩ :=
    exists_global_contDiff_extension_near_slice 3 hΩ hp (thinClosedBallAt_compact hR.le o) (hU p hp)
  obtain ⟨B, hB, WA, hWA, hpA, hAΩ, heA⟩ :=
    exists_global_contDiff_extension_near_slice 2 hΩ hp (thinClosedBallAt_compact hR.le o) (hA p hp)
  let W := WU ∩ WA
  have hWo : IsOpen W := hWU.inter hWA
  have hpW : p ∈ W := ⟨hpU,hpA⟩
  have hWΩ : W ⊆ Ω := fun q hq => hUΩ hq.1
  have hs (q : Space 3) (hq : q ∈ W) (z : ThinSpace m) (hz : z ∈ thinClosedBallAt R o) :
      thinSlice V q =ᶠ[𝓝 z] thinSlice U q := thinSlice_eventuallyEq (heU q hq.1 z hz)
  have heB (q : Space 3) (hq : q ∈ W) (z : ThinSpace m) (hz : z ∈ thinClosedBallAt R o) :
      B (q,z) = A (q,z) := (heA q hq.2 z hz).self_of_nhds
  have hμ (q : Space 3) (hq : q ∈ W) (z : ThinSpace m) (hz : z ∈ thinClosedBallAt R o) :
      currentDensity B (q,z) = currentDensity A (q,z) := by
    unfold currentDensity
    rw [heB q hq z hz]
  have hadmV : ∀ q ∈ W, ThinAdmissibleAt R o (thinSlice V q) :=
    fun q hq => (hadm q (hWΩ hq)).congr_nhds (hs q hq)
  have hEqV (q : Space 3) (hq : q ∈ W) (z : ThinSpace m) (hz : z ∈ thinBallAt R o) :
      mooreDet m (thinQuaternionHessian (thinSlice V q) z) = currentDensity B (q,z) := by
    have hz' : z ∈ thinClosedBallAt R o :=
      (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)
    rw [thinQuaternionHessian_congr_nhds (hs q hq z hz'), hμ q hq z hz']
    exact hEq q (hWΩ hq) z hz
  have hHB : ∀ y ∈ W ×ˢ thinBallAt R o, (B y).IsHermitian := by
    rintro ⟨q,z⟩ ⟨hq,hz⟩
    rw [heB q hq z (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)]
    exact hH (q,z) ⟨hWΩ hq,hz⟩
  have hdB : RealColumnConservationOn (W ×ˢ thinBallAt R o) B := by
    have hdW : RealColumnConservationOn (W ×ˢ thinBallAt R o) A :=
      fun y hy => hd y ⟨hWΩ hy.1,hy.2⟩
    apply hdW.congr_nhds
    rintro ⟨q,z⟩ ⟨hq,hz⟩
    exact heA q hq.2 z (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)
  have hF := thinValueRealAt_contDiffOn_two_of_solution hR o W (hV.of_le (by norm_num))
    (currentDensity_contDiff hB) hadmV hEqV
  have hFp := (hF p hpW).contDiffAt (hWo.mem_nhds hpW)
  have hval : (fun q => thinValueRealAt R o (thinSlice (currentDensity B) q)) =ᶠ[𝓝 p]
      (fun q => thinValueRealAt R o (thinSlice (currentDensity A) q)) := by
    filter_upwards [hWo.mem_nhds hpW] with q hq
    apply thinValueRealAt_congr_source
    intro z hz
    exact hμ q hq z (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)
  refine ⟨hFp.congr_of_eventuallyEq hval.symm, ?_⟩
  have hposV : ∀ z ∈ thinBallAt R o, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian (thinSlice V p) z) w := by
    intro z hz w hw
    rw [thinQuaternionHessian_congr_nhds (hs p hpW z (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le))]
    exact hpos p hp z hz w hw
  have hzB : ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → currentStress B (p,z) = 0 := by
    intro z hz
    unfold currentStress
    rw [heB p hpW z (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)]
    exact hzS p hp z hz
  have hmB : ∀ z ∈ thinBallAt R o, currentDensity B (p,z) = ∑ l, ρ (p,z) l := by
    intro z hz
    rw [hμ p hpW z (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)]
    exact hmass p hp z hz
  have hfB : ∀ z ∈ thinBallAt R o,
      currentFlux B (p,z) = ∑ l, ρ (p,z) l • b (p,z) l := by
    intro z hz
    unfold currentFlux
    rw [heB p hpW z (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)]
    exact hflux p hp z hz
  have hsB : ∀ z ∈ thinBallAt R o,
      currentStress B (p,z) = ∑ l, ρ (p,z) l • outer (b (p,z) l) := by
    intro z hz
    unfold currentStress
    rw [heB p hpW z (show ‖z.1-o.1‖^2+‖z.2-o.2‖^2 ≤ R^2 from hz.le)]
    exact hstress p hp z hz
  have h := thinValueRealAt_current_laplacian_nonpos_on hR o hWo hV hadmV hB hHB hdB hEqV p hpW
    hposV hzB (fun z => ρ (p,z)) (fun z => b (p,z)) (hρ p hp) hmB hfB hsB
  have hΔB : laplacian (fun q => thinValueRealAt R o (thinSlice (currentDensity B) q)) p ≤ 0 := by
    simpa only [parameterLine, secondDeriv_line_of_contDiffAt hFp, ← laplacian_space_eq_sum] using h
  rwa [Green.laplacian_congr_nhds hval] at hΔB

theorem thinValueRealAt_current_weakSuperharmonic_of_local_smoothness {m N : ℕ} {R : ℝ} (hR : 0 < R)
    (o : ThinSpace m) (Ω : Set (Space 3)) (hΩ : IsOpen Ω)
    {U : ThinCurrentSpace m → ℝ} (hU : ∀ p ∈ Ω, ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 3 U (p,z))
    (hadm : ∀ p ∈ Ω, ThinAdmissibleAt R o (thinSlice U p))
    {A : ThinCurrentSpace m → Matrix (Fin (m+1)) (Fin (m+1)) (Quaternion ℝ)}
    (hA : ∀ p ∈ Ω, ∀ z ∈ thinClosedBallAt R o, ContDiffAt ℝ 2 A (p,z)) (hH : ∀ y ∈ Ω ×ˢ thinBallAt R o, (A y).IsHermitian)
    (hd : RealColumnConservationOn (Ω ×ˢ thinBallAt R o) A)
    (hEq : ∀ p ∈ Ω, ∀ z, z ∈ thinBallAt R o →
      mooreDet m (thinQuaternionHessian (thinSlice U p) z) = currentDensity A (p,z))
    (hpos : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, ∀ w ≠ 0,
      0 < quaternionForm (thinQuaternionHessian (thinSlice U p) z) w)
    (hzS : ∀ p ∈ Ω, ∀ z, ‖z.1-o.1‖^2+‖z.2-o.2‖^2 = R^2 → currentStress A (p,z) = 0)
    (ρ : ThinCurrentSpace m → Fin N → ℝ) (b : ThinCurrentSpace m → Fin N → Fin m → Quaternion ℝ)
    (hρ : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, ∀ l, 0 ≤ ρ (p,z) l)
    (hmass : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, currentDensity A (p,z) = ∑ l, ρ (p,z) l)
    (hflux : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o, currentFlux A (p,z) = ∑ l, ρ (p,z) l • b (p,z) l)
    (hstress : ∀ p ∈ Ω, ∀ z ∈ thinBallAt R o,
      currentStress A (p,z) = ∑ l, ρ (p,z) l • QuaternionAlgebra.outer (b (p,z) l)) :
    WeakSuperharmonicOn Ω (fun p => thinValueRealAt R o (thinSlice (currentDensity A) p)) := by
  have hlocal := thinValueRealAt_current_local_regular hR o Ω hΩ hU hadm hA hH hd hEq
    hpos hzS ρ b hρ hmass hflux hstress
  exact weakSuperharmonicOn_of_contDiffOn_laplacian_nonpos hΩ
    (fun p hp => (hlocal p hp).1.contDiffWithinAt) (fun p hp => (hlocal p hp).2)

end KakeyaSharp
