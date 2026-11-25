import D9Mellin
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory Set Filter Polynomial
open scoped Topology
namespace GenesisTidalMellin

/-- One differentiation acts on the polynomial accompanying a theta summand. -/
def thetaStep (P : ℝ[X]) : ℝ[X] :=
  (C (1/2) - 2 * X) * P + 2 * X * derivative P

def weightedTerm (P : ℝ[X]) (n : ℕ) (r : ℝ) : ℝ :=
  thetaTerm n r * P.eval (thetaX n r)

def thetaSeries (P : ℝ[X]) (r : ℝ) : ℝ := ∑' n, weightedTerm P n r

theorem hasDerivAt_weightedTerm (P : ℝ[X]) (n : ℕ) (r : ℝ) :
    HasDerivAt (weightedTerm P n) (weightedTerm (thetaStep P) n r) r := by
  convert (hasDerivAt_thetaTerm n r).mul ((P.hasDerivAt _).comp r (hasDerivAt_thetaX n r)) using 1
  · rfl
  · simp [weightedTerm, thetaStep]
    ring

private theorem polynomial_exponential_bound (P : ℝ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 0, |P.eval x| ≤ C * Real.exp (x/2) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha, hpa⟩ := hp
    obtain ⟨b, hb, hqb⟩ := hq
    refine ⟨a+b, add_nonneg ha hb, fun x hx => ?_⟩
    rw [eval_add, add_mul]
    exact (abs_add_le ..).trans (add_le_add (hpa x hx) (hqb x hx))
  | monomial k a =>
    refine ⟨|a| * (2^k * (k.factorial : ℝ)), by positivity, fun x hx => ?_⟩
    have h := (div_le_iff₀ (show (0:ℝ) < k.factorial by positivity)).mp
      (Real.pow_div_factorial_le_exp (x/2) (show 0 ≤ x/2 by positivity) k)
    rw [eval_monomial, abs_mul, abs_pow, abs_of_nonneg hx]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
    calc
      x^k = (2:ℝ)^k * (x/2)^k := by rw [← mul_pow]; ring_nf
      _ ≤ 2^k * (Real.exp (x/2) * k.factorial) := by gcongr
      _ = _ := by ring

private theorem thetaX_budget (n : ℕ) {r : ℝ} (hr : -(1/8 : ℝ) < r) :
    (n:ℝ) + 3*r/2 ≤ thetaX n r / 2 := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hp := Real.pi_gt_three.le
  have he := Real.add_one_le_exp (2*r)
  have h0 : 3/4 ≤ Real.exp (2*r) := by linarith
  have hs : 1 ≤ ((n:ℝ)+1)^2 := by nlinarith [sq_nonneg (n:ℝ)]
  have h1 : 2*((n:ℝ)+1)^2 ≤ thetaX n r := by
    unfold thetaX
    calc
      _ ≤ 3*((n:ℝ)+1)^2 * (3/4) := by nlinarith [sq_nonneg ((n:ℝ)+1)]
      _ ≤ _ := by gcongr
  have h2 : 3 * Real.exp (2*r) ≤ thetaX n r := by
    unfold thetaX
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hs Real.pi_pos.le]) (Real.exp_pos _).le
  nlinarith [sq_nonneg ((n:ℝ)-1)]

theorem weightedTerm_bound (P : ℝ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n r, -(1/8:ℝ) < r →
      ‖weightedTerm P n r‖ ≤ (C * Real.exp (-r)) * Real.exp (-(n:ℝ)) := by
  obtain ⟨C,hC,h⟩ := polynomial_exponential_bound P
  refine ⟨C,hC,fun n r hr => ?_⟩
  have hx : 0 ≤ thetaX n r := by unfold thetaX; positivity
  rw [weightedTerm, thetaTerm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (r/2-thetaX n r) * (C * Real.exp (thetaX n r/2)) := by
      exact mul_le_mul_of_nonneg_left (h _ hx) (Real.exp_pos _).le
    _ = C * Real.exp (r/2-thetaX n r+thetaX n r/2) := by rw [Real.exp_add]; ring
    _ ≤ C * Real.exp (-r + -(n:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.exp_le_exp.mpr (by linarith [thetaX_budget n hr])
    _ = _ := by rw [Real.exp_add]; ring

theorem summable_weightedTerm (P : ℝ[X]) {r : ℝ} (hr : -(1/8:ℝ) < r) :
    Summable (fun n => weightedTerm P n r) := by
  obtain ⟨C,_,h⟩ := weightedTerm_bound P
  exact (Real.summable_exp_neg_nat.mul_left (C * Real.exp (-r))).of_norm_bounded
    (fun n => h n r hr)

theorem hasDerivAt_thetaSeries (P : ℝ[X]) {r : ℝ} (hr : -(1/8:ℝ) < r) :
    HasDerivAt (thetaSeries P) (thetaSeries (thetaStep P) r) r := by
  obtain ⟨C,hC,h⟩ := weightedTerm_bound (thetaStep P)
  apply hasDerivAt_tsum_of_isPreconnected
    (Real.summable_exp_neg_nat.mul_left (C * Real.exp (1/8))) isOpen_Ioi isPreconnected_Ioi
    (fun n y _ => hasDerivAt_weightedTerm P n y) _ hr (summable_weightedTerm P hr) hr
  intro n y hy
  refine (h n y hy).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by change -(1/8:ℝ) < y at hy; linarith)) hC

theorem thetaSeries_decay_bound (P : ℝ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, -(1/8:ℝ) < r → ‖thetaSeries P r‖ ≤ C * Real.exp (-r) := by
  obtain ⟨C,hC,h⟩ := weightedTerm_bound P
  refine ⟨C * ∑' n : ℕ, Real.exp (-(n:ℝ)), by positivity, fun r hr => ?_⟩
  calc
    _ ≤ ∑' n : ℕ, (C * Real.exp (-r)) * Real.exp (-(n:ℝ)) :=
      tsum_of_norm_bounded (Real.summable_exp_neg_nat.mul_left _).hasSum (fun n => h n r hr)
    _ = _ := by rw [tsum_mul_left]; ring

end GenesisTidalMellin

namespace GenesisTidalMellin
private theorem compact_term_bound (P : ℝ[X]) (x : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n r, r ∈ Ioo (x-1) (x+1) → ‖weightedTerm P n r‖ ≤ u n := by
  obtain ⟨C,hC,h⟩ := polynomial_exponential_bound P
  let a := Real.exp (2*(x-1))
  have ha : 0 < a := Real.exp_pos _
  refine ⟨fun n => (C*Real.exp ((x+1)/2))*Real.exp ((n:ℝ)*(-a)),
    (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr ha)).mul_left _, fun n r hr => ?_⟩
  have hx : 0 ≤ thetaX n r := by unfold thetaX; positivity
  have he : a ≤ Real.exp (2*r) := Real.exp_le_exp.mpr (by linarith [hr.1])
  have hp : 2*(n:ℝ) ≤ Real.pi*((n:ℝ)+1)^2 := by
    have hn := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg ((n:ℝ)+1))
    nlinarith [sq_nonneg (n:ℝ)]
  have hX : (2*(n:ℝ))*a ≤ thetaX n r :=
    mul_le_mul hp he ha.le (by positivity)
  rw [weightedTerm, thetaTerm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (r/2-thetaX n r) * (C * Real.exp (thetaX n r/2)) :=
      mul_le_mul_of_nonneg_left (h _ hx) (Real.exp_pos _).le
    _ = C * Real.exp (r/2-thetaX n r+thetaX n r/2) := by rw [Real.exp_add]; ring
    _ ≤ C * Real.exp ((x+1)/2 + (n:ℝ)*(-a)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.exp_le_exp.mpr (by nlinarith [hr.2])
    _ = _ := by rw [Real.exp_add]; ring

theorem thetaSeries_derivative (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (thetaSeries P) (thetaSeries (thetaStep P) x) x := by
  have hx : x ∈ Ioo (x-1) (x+1) := ⟨by linarith, by linarith⟩
  obtain ⟨u,hu,hd⟩ := compact_term_bound (thetaStep P) x
  obtain ⟨v,hv,hb⟩ := compact_term_bound P x
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hasDerivAt_weightedTerm P n y) hd hx
    (hv.of_norm_bounded (fun n => hb n x hx)) hx

end GenesisTidalMellin
#print axioms GenesisTidalMellin.thetaSeries_derivative

namespace GenesisTidalMellin
theorem summable_weightedTerm_all (P : ℝ[X]) (x : ℝ) : Summable (fun n => weightedTerm P n x) := by
  obtain ⟨u,hu,h⟩ := compact_term_bound P x
  exact hu.of_norm_bounded fun n => h n x ⟨by linarith, by linarith⟩
end GenesisTidalMellin
