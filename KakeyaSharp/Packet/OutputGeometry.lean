/- Modified for the Palomar submission: module header, public imports,
and exposed public declarations. Original proof bodies are retained.
See MODULE_MIGRATION.json for the checkpoint and ported file hashes. -/
module

public import KakeyaSharp.Packet.CoverIntegral

@[expose] public section

/-! A fixed compact spatial net and the disjoint physical balls required
by the localized output theorem. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace KakeyaSharp.Packet
open Set Metric MeasureTheory OAI.Analysis.PDE.Concentration

def sliceSupportRadius (A : ℝ) : ℝ := Real.sqrt A+1
def outputBallRadius (δ : ℝ) : ℝ := (1/100 : ℝ)*δ^3
def outputThickness (δ : ℝ) : ℝ := (1/1000 : ℝ)*δ^4
def outputCenter {m : ℕ} (δ : ℝ) (b : Space m) : ThinSpace m := (δ^2 • b,0)

theorem graphAxis_norm_le {m : ℕ} {A t : ℝ} (hA : 0 ≤ A)
    (a v : Fin m → ℝ) (ha : (∑ j, (a j)^2) ≤ A)
    (hv : (∑ j, (v j)^2) ≤ 1/16) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖graphAxis a v t‖ ≤ Real.sqrt A+1/4 := by
  have ha' : ‖(WithLp.toLp 2 a : Space m)‖^2 ≤ A := by
    simpa only [EuclideanSpace.real_norm_sq_eq] using ha
  have hv' : ‖(WithLp.toLp 2 v : Space m)‖^2 ≤ 1/16 := by
    simpa only [EuclideanSpace.real_norm_sq_eq] using hv
  have han : ‖(WithLp.toLp 2 a : Space m)‖ ≤ Real.sqrt A := by
    nlinarith [Real.sq_sqrt hA,Real.sqrt_nonneg A,norm_nonneg (WithLp.toLp 2 a : Space m)]
  have hvn : ‖(WithLp.toLp 2 v : Space m)‖ ≤ 1/4 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 v : Space m)]
  calc
    _ ≤ ‖(WithLp.toLp 2 a : Space m)‖+‖t • (WithLp.toLp 2 v : Space m)‖ := norm_add_le _ _
    _ = ‖(WithLp.toLp 2 a : Space m)‖+t*‖(WithLp.toLp 2 v : Space m)‖ := by
      rw [norm_smul,Real.norm_of_nonneg ht.1]
    _ ≤ _ := by nlinarith [norm_nonneg (WithLp.toLp 2 v : Space m),ht.2]

theorem sliceOverlap_support {m N : ℕ} {δ A t : ℝ} (hδ1 : δ ≤ 1) (hA : 0 ≤ A)
    (a v : Fin N → Fin m → ℝ) (weights : Fin N → ℝ)
    (ha : ∀ l, (∑ j, (a l j)^2) ≤ A) (hv : ∀ l, (∑ j, (v l j)^2) ≤ 1/16)
    (ht : t ∈ Icc (0 : ℝ) 1) {x : Space m} (hx : sliceOverlap δ a v weights t x ≠ 0) :
    x ∈ closedBall 0 (sliceSupportRadius A) := by
  obtain ⟨l,_,hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  have hd : dist x (graphAxis (a l) (v l) t) ≤ δ/64 := by
    by_contra hn
    simp only [hn,ite_false,ne_eq,not_true_eq_false] at hl
  have hg := graphAxis_norm_le hA (a l) (v l) (ha l) (hv l) ht
  have htri := dist_triangle x (graphAxis (a l) (v l) t) 0
  simp only [dist_zero_right] at htri
  rw [mem_closedBall,dist_zero_right]
  change ‖x‖ ≤ Real.sqrt A+1
  linarith

theorem output_ball_in_outer {m : ℕ} {δ A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A)
    {b : Space m} (hb : b ∈ closedBall 0 (sliceSupportRadius A)) :
    thinClosedBallAt (outputBallRadius δ) (outputCenter δ b) ⊆
      thinBallAt (propagationOuterRadius A (1/16)) 0 := by
  have hb' : ‖b‖ ≤ Real.sqrt A+1 := by simpa [sliceSupportRadius] using hb
  have hb2 : ‖b‖^2 ≤ 2*A+2 := by
    nlinarith [Real.sq_sqrt hA,Real.sqrt_nonneg A,norm_nonneg b,sq_nonneg (Real.sqrt A-1)]
  have hd4 : δ^4 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hd6 : δ^6 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hc : ‖(δ^2) • b‖^2 ≤ 2*A+2 := by
    rw [norm_smul,Real.norm_of_nonneg (sq_nonneg δ),mul_pow]
    nlinarith [sq_nonneg ‖b‖,mul_le_mul_of_nonneg_right hd4 (sq_nonneg ‖b‖)]
  intro z hz
  have hz' : ‖z.1-δ^2 • b‖^2+‖z.2‖^2 ≤ ((1/100 : ℝ)*δ^3)^2 := by
    simpa [thinClosedBallAt,outputCenter,outputBallRadius] using hz
  have hx := norm_add_le (z.1-δ^2 • b) (δ^2 • b)
  rw [sub_add_cancel] at hx
  have hx2 : ‖z.1‖^2 ≤ 2*‖z.1-δ^2 • b‖^2+2*‖δ^2 • b‖^2 := by
    nlinarith [norm_nonneg z.1,norm_nonneg (z.1-δ^2 • b),norm_nonneg (δ^2 • b),
      sq_nonneg (‖z.1-δ^2 • b‖-‖δ^2 • b‖)]
  have hout := propagationOuterRadius_sq_gt A (1/16)
  change ‖z.1-0‖^2+‖z.2-0‖^2 < propagationOuterRadius A (1/16)^2
  simp only [sub_zero]
  nlinarith [sq_nonneg ‖z.2‖]

theorem output_balls_disjoint {m J : ℕ} {δ : ℝ} (hδ : 0 < δ) (b : Fin J → Space m)
    (hsep : ∀ i j, i ≠ j → δ/32 < dist (b i) (b j)) :
    Pairwise (fun i j => Disjoint
      (thinBallAt (outputBallRadius δ) (outputCenter δ (b i)))
      (thinBallAt (outputBallRadius δ) (outputCenter δ (b j)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  have hx (k : Fin J) (hk : z ∈ thinBallAt (outputBallRadius δ) (outputCenter δ (b k))) :
      dist z.1 (δ^2 • b k) < outputBallRadius δ := by
    have he : ‖z.1-δ^2 • b k‖^2+‖z.2‖^2 < (outputBallRadius δ)^2 := by
      simpa [thinBallAt,outputCenter] using hk
    rw [dist_eq_norm]
    have hr : 0 < outputBallRadius δ := by unfold outputBallRadius; positivity
    nlinarith [sq_nonneg ‖z.2‖,norm_nonneg (z.1-δ^2 • b k)]
  have htri := dist_triangle (δ^2 • b i) z.1 (δ^2 • b j)
  rw [dist_comm (δ^2 • b i) z.1] at htri
  have hd : dist (δ^2 • b i) (δ^2 • b j) = δ^2*dist (b i) (b j) := by
    rw [dist_eq_norm,← smul_sub,norm_smul,Real.norm_of_nonneg (sq_nonneg δ),dist_eq_norm]
  rw [hd] at htri
  have hs := mul_lt_mul_of_pos_left (hsep i j hij) (sq_pos_of_pos hδ)
  have hi' := hx i hi
  have hj' := hx j hj
  unfold outputBallRadius at hi' hj'
  nlinarith [pow_pos hδ 3]

theorem outputAxis_at_time {m : ℕ} (δ t θ : ℝ) (a v : Fin m → ℝ) :
    outputAxis δ a v (cylinderPoint (1+δ^2*t) (δ^4) θ) = δ^2 • graphAxis a v t := by
  ext j
  simp [outputAxis,graphAxis,cylinderPoint,cylinderRadial,cylinderAxis,EuclideanSpace.basisFun_apply]
  ring

theorem output_parameter_radius {m : ℕ} {δ : ℝ} (hδ : 0 < δ) (t θ : ℝ) :
    radius (cylinderPoint (1+δ^2*t) (δ^4) θ,(0 : ThinSpace m))=δ^4 := by
  have he : ((δ^4)*Real.cos θ)^2+((δ^4)*Real.sin θ)^2=(δ^4)^2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  simp only [radius,cylinderPoint,cylinderRadial,cylinderAxis,EuclideanSpace.basisFun_apply]
  simp [he,Real.sqrt_sq_eq_abs,abs_of_pos (pow_pos hδ 4)]

end KakeyaSharp.Packet
