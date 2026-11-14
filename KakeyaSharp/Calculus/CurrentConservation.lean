/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Green.GreenOperator

@[expose] public section

/-! Differentiating the two first-order conservation laws gives the precise
second-order identity used in scalar transfer. All derivatives are actual
Frechet derivatives along fixed directions. -/
noncomputable section
namespace KakeyaSharp.Current
open KakeyaSharp.Green
open scoped ContDiff

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]

theorem contDiff_directional {f : E → ℝ} (hf : ContDiff ℝ 2 f) (v : E) :
    ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem fderiv_sum_directional (f : I → E → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (d : I → E) (x v : E) :
    fderiv ℝ (fun y => ∑ i, fderiv ℝ (f i) y (d i)) x v =
      ∑ i, fderiv ℝ (fderiv ℝ (f i)) x v (d i) := by
  rw [fderiv_fun_sum (fun i _ => (contDiff_directional (hf i) (d i)).differentiable (by norm_num) x)]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact directional_twice (hf i) v (d i) x

theorem double_conservation {T S : Type*} [Fintype T] [Fintype S]
    (dt : T → E) (ds : S → E) (ρ : E → ℝ)
    (ξ : T → S → E → ℝ) (A : S → S → E → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (hξ : ∀ a j, ContDiff ℝ 2 (ξ a j))
    (hA : ∀ i j, ContDiff ℝ 2 (A i j))
    (hmass : ∀ x a, fderiv ℝ ρ x (dt a) +
      ∑ j, fderiv ℝ (ξ a j) x (ds j) = 0)
    (hmomentum : ∀ x j, (∑ a, fderiv ℝ (ξ a j) x (dt a)) +
      ∑ i, fderiv ℝ (A i j) x (ds i) = 0) (x : E) :
    (∑ a, fderiv ℝ (fderiv ℝ ρ) x (dt a) (dt a)) =
      ∑ j, ∑ i, fderiv ℝ (fderiv ℝ (A i j)) x (ds j) (ds i) := by
  have hmass2 (a : T) : fderiv ℝ (fderiv ℝ ρ) x (dt a) (dt a) +
      ∑ j, fderiv ℝ (fderiv ℝ (ξ a j)) x (dt a) (ds j) = 0 := by
    have he : (fun y => fderiv ℝ ρ y (dt a) +
        ∑ j, fderiv ℝ (ξ a j) y (ds j)) = (fun _ => (0 : ℝ)) := by
      funext y
      exact hmass y a
    have hs : ContDiff ℝ 1 (fun y => ∑ j, fderiv ℝ (ξ a j) y (ds j)) :=
      ContDiff.sum (fun j _ => contDiff_directional (hξ a j) (ds j))
    have h := congrArg (fun f => fderiv ℝ f x (dt a)) he
    rw [fderiv_fun_add ((contDiff_directional hρ (dt a)).differentiable (by norm_num) x)
      (hs.differentiable (by norm_num) x)] at h
    simpa only [_root_.add_apply, directional_twice hρ,
      fderiv_sum_directional _ (hξ a), fderiv_const_apply, _root_.zero_apply] using h
  have hmom2 (j : S) : (∑ a, fderiv ℝ (fderiv ℝ (ξ a j)) x (ds j) (dt a)) =
      -(∑ i, fderiv ℝ (fderiv ℝ (A i j)) x (ds j) (ds i)) := by
    have he : (fun y => (∑ a, fderiv ℝ (ξ a j) y (dt a)) +
        ∑ i, fderiv ℝ (A i j) y (ds i)) = (fun _ => (0 : ℝ)) := by
      funext y
      exact hmomentum y j
    have ht : ContDiff ℝ 1 (fun y => ∑ a, fderiv ℝ (ξ a j) y (dt a)) :=
      ContDiff.sum (fun a _ => contDiff_directional (hξ a j) (dt a))
    have hs : ContDiff ℝ 1 (fun y => ∑ i, fderiv ℝ (A i j) y (ds i)) :=
      ContDiff.sum (fun i _ => contDiff_directional (hA i j) (ds i))
    have h := congrArg (fun f => fderiv ℝ f x (ds j)) he
    rw [fderiv_fun_add (ht.differentiable (by norm_num) x)
      (hs.differentiable (by norm_num) x)] at h
    simp only [_root_.add_apply, fderiv_sum_directional _ (fun a => hξ a j),
      fderiv_sum_directional _ (fun i => hA i j), fderiv_const_apply, _root_.zero_apply] at h
    linarith
  calc
    (∑ a, fderiv ℝ (fderiv ℝ ρ) x (dt a) (dt a)) =
        -(∑ a, ∑ j, fderiv ℝ (fderiv ℝ (ξ a j)) x (dt a) (ds j)) := by
      have h := congrArg (fun f : T → ℝ => ∑ a, f a) (funext hmass2)
      simp only [Finset.sum_add_distrib, Finset.sum_const_zero] at h
      linarith
    _ = -(∑ j, ∑ a, fderiv ℝ (fderiv ℝ (ξ a j)) x (ds j) (dt a)) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      exact ((hξ a j).contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (dt a) (ds j)
    _ = _ := by simp only [hmom2, Finset.sum_neg_distrib, neg_neg]

end KakeyaSharp.Current
