import ThetaJets
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite

noncomputable section
open Polynomial Set Filter
namespace GenesisTidalMellin
namespace DirectSigns
set_option maxHeartbeats 3000000
private theorem q0 : Q 0 = 2*X^2 - 3*X := by
  change phiPoly = _
  unfold phiPoly
  ring
private theorem q1 : Q 1 = -4*X^3 + 15*X^2 - C (15/2)*X := by
  change thetaStep (Q 0) = _
  rw [q0]
  apply Polynomial.funext
  intro z
  norm_num [thetaStep, Polynomial.derivative_X_pow, Polynomial.derivative_mul]
  ring
private theorem q2 : Q 2 = 8*X^4 - 56*X^3 + C (165/2)*X^2 - C (75/4)*X := by
  change thetaStep (Q 1) = _
  rw [q1]
  apply Polynomial.funext
  intro z
  norm_num [thetaStep, Polynomial.derivative_X_pow, Polynomial.derivative_mul]
  ring
private theorem q3 : Q 3 = -16*X^5 + 180*X^4 - 529*X^3 + C (1635/4)*X^2 - C (375/8)*X := by
  change thetaStep (Q 2) = _
  rw [q2]
  apply Polynomial.funext
  intro z
  norm_num [thetaStep, Polynomial.derivative_X_pow, Polynomial.derivative_mul]
  ring
private theorem q4 : Q 4 = 32*X^6 - 528*X^5 + 2588*X^4 - 4256*X^3 + C (15465/8)*X^2 - C (1875/16)*X := by
  change thetaStep (Q 3) = _
  rw [q3]
  apply Polynomial.funext
  intro z
  norm_num [thetaStep, Polynomial.derivative_X_pow, Polynomial.derivative_mul]
  ring
private theorem q5 : Q 5 = -64*X^7 + 1456*X^6 - 10720*X^5 + 30510*X^4 - C (126121/4)*X^3 + C (142935/16)*X^2 - C (9375/32)*X := by
  change thetaStep (Q 4) = _
  rw [q4]
  apply Polynomial.funext
  intro z
  norm_num [thetaStep, Polynomial.derivative_X_pow, Polynomial.derivative_mul]
  ring
private theorem q6 : Q 6 = 128*X^8 - 3840*X^7 + 39640*X^6 - 173580*X^5 + C (644791/2)*X^4 - C (445627/2)*X^3 + C (1305165/32)*X^2 - C (46875/64)*X := by
  change thetaStep (Q 5) = _
  rw [q5]
  apply Polynomial.funext
  intro z
  norm_num [thetaStep, Polynomial.derivative_X_pow, Polynomial.derivative_mul]
  ring
private theorem q7 : Q 7 = -256*X^9 + 9792*X^8 - 134960*X^7 + 842660*X^6 - 2467381*X^5 + C (12743955/4)*X^4 - C (24477769/16)*X^3 + C (11840235/64)*X^2 - C (234375/128)*X := by
  change thetaStep (Q 6) = _
  rw [q6]
  apply Polynomial.funext
  intro z
  norm_num [thetaStep, Polynomial.derivative_X_pow, Polynomial.derivative_mul]
  ring
private theorem q8 : Q 8 = 512*X^10 - 24320*X^9 + 431488*X^8 - 3642240*X^7 + 15468012*X^6 - 32279478*X^5 + C (60281251/2)*X^4 - 10314101*X^3 + C (107030865/128)*X^2 - C (1171875/256)*X := by
  change thetaStep (Q 7) = _
  rw [q7]
  apply Polynomial.funext
  intro z
  norm_num [thetaStep, Polynomial.derivative_X_pow, Polynomial.derivative_mul]
  ring

private def lowerExp (x : ℝ) := 8000*(1 + 3*(x-3) + (3*(x-3))^2/2)

private theorem lowerExp_le {x : ℝ} (hx : 3 ≤ x) : lowerExp x ≤ Real.exp (3*x) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 9) 20
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at he
  have he' : (8000:ℝ) ≤ Real.exp 9 := by linarith only [he]
  have hy : 0 ≤ 3*(x-3) := by linarith
  have ht := Real.sum_le_exp_of_nonneg hy 3
  simp [Finset.sum_range_succ, Nat.factorial_succ] at ht
  rw [show 3*x = 9 + 3*(x-3) by ring, Real.exp_add]
  unfold lowerExp
  apply mul_le_mul he' _ (by positivity) (Real.exp_pos _).le
  linarith only [ht]

/-- For 0 ≤ r ≤ 1/5 the leading theta argument lies between 3 and 47/10. -/
private theorem near_range {r : ℝ} (hr : 0 ≤ r) (hb : r ≤ 1/5) :
    3 ≤ thetaX 0 r ∧ thetaX 0 r ≤ 47/10 := by
  have he := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 2/5) (by norm_num) (n:=6) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at he
  have hπ := Real.pi_lt_d4
  have hl := Real.one_le_exp (by linarith : 0 ≤ 2*r)
  have hu := Real.exp_le_exp.mpr (by linarith : 2*r ≤ 2/5)
  simp only [thetaX, Nat.cast_zero, zero_add, one_pow, mul_one]
  constructor
  · exact Real.pi_gt_three.le.trans (le_mul_of_one_le_right Real.pi_pos.le hl)
  · nlinarith only [mul_le_mul hπ.le (hu.trans he) (Real.exp_pos _).le (by norm_num)]

private theorem q8_head {x : ℝ} (ha : 3 ≤ x) (hb : x ≤ 47/10) :
    0 < (Q 8).eval x := by
  have hL : 0 ≤ x-3 := sub_nonneg.mpr ha
  have hR : 0 ≤ 47/10-x := sub_nonneg.mpr hb
  have he : (Q 8).eval x = (134780680301/50000) + ((47/10-x)*(797656926077/80000) + (x-3)*((47/10-x)*(927355733987/16000) + (x-3)*((47/10-x)*(7607284471/100) + (x-3)*((47/10-x)*(388633963/10) + (x-3)*((47/10-x)*6685854 + (x-3)*((x-3)*(1267308 + (x-3)*((2182656/5) + (47/10-x)*33024 + (x-3)*((47/10-x)*8960 + (x-3)*((x-3)*(512))))))))))) := by
    simp only [q8, eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_ofNat, eval_X, eval_C, lowerExp]
    ring
  rw [he]
  positivity

private theorem q8_pair {x : ℝ} (ha : 3 ≤ x) (hb : x ≤ 47/10) :
    0 < lowerExp x * (Q 8).eval x + (Q 8).eval (4*x) := by
  have hL : 0 ≤ x-3 := sub_nonneg.mpr ha
  have hR : 0 ≤ 47/10-x := sub_nonneg.mpr hb
  have he : lowerExp x * (Q 8).eval x + (Q 8).eval (4*x) = (10192605107247/64) + ((x-3)*((27577721216205/64) + (x-3)*((2112527506438089/5000) + (47/10-x)*(206672517686583/500) + (x-3)*((47/10-x)*(158229808890723/100) + (x-3)*((47/10-x)*(7910662144872/5) + (x-3)*((47/10-x)*531082957392 + (x-3)*((x-3)*(86514426432 + (x-3)*(130881360768 + (x-3)*((127684042752/5) + (47/10-x)*842047488 + (x-3)*((47/10-x)*310272000 + (x-3)*((x-3)*(18432000))))))))))))) := by
    simp only [q8, eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_ofNat, eval_X, eval_C, lowerExp]
    ring
  rw [he]
  positivity

private theorem q8_tail {x : ℝ} (h : 19 ≤ x) : 0 < (Q 8).eval x := by
  let z := x-19
  have hz : 0 ≤ z := sub_nonneg.mpr h
  have hx : x = 19+z := by dsimp [z]; ring
  rw [hx, q8]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_ofNat, eval_X, eval_C]
  ring_nf
  positivity

/-- At every radius r ≥ 1/5, each individual theta summand gives a strictly
positive contribution to the ninth-dimensional numerator. -/
private theorem middle_poly {r x : ℝ} (hr : 1/5 ≤ r)
    (hb : (937/200:ℝ)*(1+2*(r-1/5)+2*(r-1/5)^2) ≤ x) :
    0 < r^3*(Q 4).eval x - 6*r^2*(Q 3).eval x + 15*r*(Q 2).eval x - 15*(Q 1).eval x := by
  let z := r-1/5
  let u := x-(937/200)*(1+2*z+2*z^2)
  have hz : 0 ≤ z := sub_nonneg.mpr hr
  have hu : 0 ≤ u := sub_nonneg.mpr hb
  have hr' : r = 1/5 + z := by dsimp [z]; ring
  have hx : x = (937/200)*(1+2*z+2*z^2) + u := by dsimp [u]; ring
  rw [hr', hx, q1, q2, q3, q4]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_ofNat, eval_X, eval_C]
  ring_nf
  positivity

private theorem middle_argument {r : ℝ} (hr : 1/5 ≤ r) (n : ℕ) :
    (937/200:ℝ)*(1+2*(r-1/5)+2*(r-1/5)^2) ≤ thetaX n r := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2/5) 6
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at he
  have hπ := Real.pi_gt_d4
  have hbase : (937/200:ℝ) ≤ Real.pi * Real.exp (2/5) := by
    nlinarith only [mul_le_mul hπ.le he (by norm_num) Real.pi_pos.le]
  have hnn : (1:ℝ) ≤ ((n:ℝ)+1)^2 := by
    have hn : 0 ≤ (n:ℝ) := by positivity
    nlinarith [sq_nonneg (n:ℝ)]
  have hz : 0 ≤ r-1/5 := sub_nonneg.mpr hr
  have ht := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ 2*(r-1/5)) 3
  simp [Finset.sum_range_succ, Nat.factorial_succ] at ht
  have ht' : 1+2*(r-1/5)+2*(r-1/5)^2 ≤ Real.exp (2*(r-1/5)) := by linarith only [ht]
  unfold thetaX
  rw [show 2*r = 2/5 + 2*(r-1/5) by ring, Real.exp_add]
  calc
    _ ≤ (Real.pi * Real.exp (2/5)) * Real.exp (2*(r-1/5)) :=
      mul_le_mul hbase ht' (by positivity) (by positivity)
    _ = (Real.pi * (1:ℝ)) * (Real.exp (2/5) * Real.exp (2*(r-1/5))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnn Real.pi_pos.le) (by positivity)

theorem near_eighth {r : ℝ} (hr : 0 ≤ r) (hb : r ≤ 1/5) : 0 < p 8 r := by
  let x := thetaX 0 r
  have h := near_range hr hb
  have h1 : thetaX 1 r = 4*x := by simp [x, thetaX]; ring
  have hp := q8_head h.1 h.2
  have hp' := q8_pair h.1 h.2
  have he := mul_le_mul_of_nonneg_right (lowerExp_le h.1) hp.le
  have hs : 0 < Real.exp (3*x) * (Q 8).eval x + (Q 8).eval (4*x) := by linarith only [hp', he]
  have hpair : 0 < weightedTerm (Q 8) 0 r + weightedTerm (Q 8) 1 r := by
    have hx : Real.exp (r/2 - x) = Real.exp (r/2 - 4*x) * Real.exp (3*x) := by
      rw [← Real.exp_add]; congr 1; ring
    change 0 < Real.exp (r/2-x) * (Q 8).eval x + Real.exp (r/2-thetaX 1 r) * (Q 8).eval (thetaX 1 r)
    rw [h1,hx]
    nlinarith only [mul_pos (Real.exp_pos (r/2-4*x)) hs]
  have ht (n : ℕ) : 0 ≤ weightedTerm (Q 8) (n+2) r := by
    have hsq : (9:ℝ) ≤ ((↑(n+2 : ℕ):ℝ)+1)^2 := by
      push_cast
      have hn : 0 ≤ (n:ℝ) := by positivity
      nlinarith [sq_nonneg (n:ℝ)]
    have hx : 19 ≤ thetaX (n+2) r := by
      unfold thetaX
      have hu := Real.one_le_exp (by linarith : 0 ≤ 2*r)
      have hs' := mul_le_mul Real.pi_gt_three.le hsq (by norm_num) Real.pi_pos.le
      nlinarith only [hs', le_mul_of_one_le_right (by positivity : 0 ≤ Real.pi * ((↑(n+2 : ℕ):ℝ)+1)^2) hu]
    exact (mul_pos (Real.exp_pos _) (q8_tail hx)).le
  have hsplit := (summable_weightedTerm_all (Q 8) r).sum_add_tsum_nat_add 2
  change 0 < ∑' n, weightedTerm (Q 8) n r
  rw [← hsplit]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  exact add_pos_of_pos_of_nonneg hpair (tsum_nonneg ht)

theorem positive_middle {r : ℝ} (hr : 1/5 ≤ r) :
    0 < r^3*p 4 r - 6*r^2*p 3 r + 15*r*p 2 r - 15*p 1 r := by
  let w (j n : ℕ) := weightedTerm (Q j) n r
  let v (n : ℕ) := r^3*w 4 n - 6*r^2*w 3 n + 15*r*w 2 n - 15*w 1 n
  have hw (j : ℕ) : HasSum (w j) (p j r) := (summable_weightedTerm_all (Q j) r).hasSum
  have hv : HasSum v (r^3*p 4 r - 6*r^2*p 3 r + 15*r*p 2 r - 15*p 1 r) :=
    (((((hw 4).mul_left (r^3)).sub ((hw 3).mul_left (6*r^2))).add
      ((hw 2).mul_left (15*r))).sub ((hw 1).mul_left 15))
  have hpos (n : ℕ) : 0 < v n := by
    have hp := mul_pos (Real.exp_pos (r/2-thetaX n r)) (middle_poly hr (middle_argument hr n))
    dsimp [v,w,weightedTerm,thetaTerm]
    linarith only [hp]
  rw [← hv.tsum_eq]
  exact hv.summable.tsum_pos (fun n => (hpos n).le) 0 (hpos 0)

end DirectSigns
end GenesisTidalMellin
#print axioms GenesisTidalMellin.DirectSigns.near_eighth
#print axioms GenesisTidalMellin.DirectSigns.positive_middle
