/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.GraphCoordinates

@[expose] public section

/-! The slope chart near a fixed unit direction, including the quantitative
separation estimate needed to apply the graph-tube theorem. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Graph
open Set Metric

def north (m : ℕ) : Space (m+1) := insert 1 0
def slope {m : ℕ} (v : Space (m+1)) : Space m := (v 0)⁻¹ • tail v

theorem norm_north (m : ℕ) : ‖north m‖=1 := by
  have h := norm_sq_head_tail (north m)
  simp only [north,insert_zero,tail_insert,norm_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero,one_pow] at h
  change ‖insert 1 (0 : Space m)‖=1
  nlinarith [norm_nonneg (insert 1 (0 : Space m))]

theorem norm_insert_one_ge_one {m : ℕ} (u : Space m) : 1 ≤ ‖insert 1 u‖ := by
  simpa only [insert_zero,abs_one] using abs_head_le_norm (insert 1 u)

theorem normalize_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (hu : 1 ≤ ‖u‖) (hv : 0 < ‖v‖) :
    ‖‖u‖⁻¹ • u-‖v‖⁻¹ • v‖ ≤ 2*‖u-v‖ := by
  have hu0 : 0 < ‖u‖ := by linarith
  have hi : 0 ≤ ‖u‖⁻¹ := inv_nonneg.mpr hu0.le
  have he : (‖u‖⁻¹-‖v‖⁻¹)*‖v‖=‖u‖⁻¹*(‖v‖-‖u‖) := by
    field_simp [hu0.ne',hv.ne']
  have habs : abs (‖u‖⁻¹-‖v‖⁻¹)*‖v‖=‖u‖⁻¹*abs (‖v‖-‖u‖) := by
    have h := congrArg abs he
    simpa only [abs_mul,abs_of_nonneg (norm_nonneg v),abs_of_nonneg hi] using h
  have hvec : ‖u‖⁻¹ • u-‖v‖⁻¹ • v =
      ‖u‖⁻¹ • (u-v)+(‖u‖⁻¹-‖v‖⁻¹) • v := by
    rw [smul_sub,sub_smul]
    abel
  have hnorm : |‖v‖-‖u‖| ≤ ‖u-v‖ := by
    simpa only [abs_sub_comm] using abs_norm_sub_norm_le u v
  have hInv : ‖u‖⁻¹ ≤ 1 := (inv_le_one₀ hu0).mpr hu
  calc
    _ = ‖‖u‖⁻¹ • (u-v)+(‖u‖⁻¹-‖v‖⁻¹) • v‖ := by rw [hvec]
    _ ≤ ‖‖u‖⁻¹ • (u-v)‖+‖(‖u‖⁻¹-‖v‖⁻¹) • v‖ := norm_add_le _ _
    _ = ‖u‖⁻¹*‖u-v‖+‖u‖⁻¹*|‖v‖-‖u‖| := by
      rw [norm_smul,norm_smul,Real.norm_of_nonneg hi,Real.norm_eq_abs,habs]
    _ ≤ ‖u‖⁻¹*‖u-v‖+‖u‖⁻¹*‖u-v‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm hi)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hInv (norm_nonneg (u-v))]

theorem insert_slope_eq {m : ℕ} {v : Space (m+1)} (hv0 : 0 < v 0) :
    insert 1 (slope v)=(v 0)⁻¹ • v := by
  ext j
  cases j using Fin.cases <;> simp [insert,slope,tail,hv0.ne',mul_comm]

theorem normalize_slope_eq {m : ℕ} {v : Space (m+1)} (hv : ‖v‖=1) (hv0 : 0 < v 0) :
    ‖insert 1 (slope v)‖⁻¹ • insert 1 (slope v)=v := by
  rw [insert_slope_eq hv0,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hv0.le),
    hv,mul_one,inv_inv,smul_smul,mul_inv_cancel₀ hv0.ne',one_smul]

theorem direction_dist_le_slope_dist {m : ℕ} {v w : Space (m+1)}
    (hv : ‖v‖=1) (hw : ‖w‖=1) (hv0 : 0 < v 0) (hw0 : 0 < w 0) :
    dist v w ≤ 2*dist (slope v) (slope w) := by
  have h := normalize_sub_le (insert 1 (slope v)) (insert 1 (slope w))
    (norm_insert_one_ge_one _) (lt_of_lt_of_le (by norm_num) (norm_insert_one_ge_one _))
  rw [normalize_slope_eq hv hv0,normalize_slope_eq hw hw0] at h
  have he : insert 1 (slope v)-insert 1 (slope w)=insert 0 (slope v-slope w) := by
    ext j
    cases j using Fin.cases <;> simp [insert]
  rw [he,norm_insert_zero] at h
  simpa only [dist_eq_norm] using h

theorem small_slope_of_near_north {m : ℕ} {v : Space (m+1)}
    (hnear : dist v (north m) ≤ 1/16) :
    0 < v 0 ∧ ‖slope v‖ ≤ 1/4 := by
  have hh : |v 0-1| ≤ 1/16 := by
    have h := abs_head_le_norm (v-north m)
    have hh' : |v 0-1| ≤ ‖v-north m‖ := by simpa [north,insert] using h
    exact hh'.trans (show ‖v-north m‖ ≤ 1/16 from hnear)
  have hhead : 15/16 ≤ v 0 := by linarith [(abs_le.mp hh).1]
  have hv0 : 0 < v 0 := by linarith
  have ht : ‖tail v‖ ≤ 1/16 := by
    have h := dist_tail_le v (north m)
    simpa only [north,tail_insert,dist_zero_right] using h.trans hnear
  refine ⟨hv0,?_⟩
  rw [slope,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hv0.le)]
  have hdiv : ‖tail v‖/(v 0) ≤ 1/4 := (div_le_iff₀ hv0).mpr (by linarith)
  simpa only [div_eq_inv_mul] using hdiv

theorem slope_sq_sum_of_near_north {m : ℕ} {v : Space (m+1)}
    (hnear : dist v (north m) ≤ 1/16) :
    (∑ j, (slope v j)^2) ≤ 1/16 := by
  have h := (small_slope_of_near_north hnear).2
  rw [← EuclideanSpace.real_norm_sq_eq]
  nlinarith [norm_nonneg (slope v)]

theorem slope_separated {m N : ℕ} {δ : ℝ} (v : Fin N → Space (m+1))
    (hv : ∀ l, ‖v l‖=1) (hnear : ∀ l, dist (v l) (north m) ≤ 1/16)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) :
    ∀ i j, i ≠ j → δ/2 ≤ dist (slope (v i)) (slope (v j)) := by
  intro i j hij
  have h := direction_dist_le_slope_dist (hv i) (hv j)
    (small_slope_of_near_north (hnear i)).1 (small_slope_of_near_north (hnear j)).1
  linarith [hsep i j hij]

end KakeyaSharp.Graph
