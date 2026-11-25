import ThetaCosine
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
namespace GenesisTidalMellin
open Polynomial Filter
open scoped Topology

def Q : ℕ → ℝ[X]
  | 0 => phiPoly
  | n+1 => thetaStep (Q n)

def p (j : ℕ) := thetaSeries (Q j)

theorem dp (j : ℕ) (r : ℝ) : HasDerivAt (p j) (p (j+1) r) r :=
  thetaSeries_derivative _ _

theorem p_decay (j : ℕ) : Tendsto (p j) atTop (𝓝 0) := by
  simpa [p] using thetaSeries_mul_tendsto (Q j) (b := fun _ => 1) (by simp)

theorem p_iter (j : ℕ) : iteratedDeriv j phi = p j := by
  induction j with
  | zero => simp [p,Q]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun r => (dp j r).deriv

private theorem ode_all (r : ℝ) :
    thetaSeries (thetaStep (thetaStep 1)) r - g r / 4 = 2 * phi r := by
  have htt (n : ℕ) : weightedTerm (thetaStep (thetaStep 1)) n r =
      (1/4:ℝ) * weightedTerm 1 n r + 2 * weightedTerm phiPoly n r := by
    simp [thetaStep, weightedTerm, phiPoly, Polynomial.derivative_mul]
    ring
  change (∑' n, weightedTerm (thetaStep (thetaStep 1)) n r) - (∑' n, weightedTerm 1 n r)/4 =
    2 * ∑' n, weightedTerm phiPoly n r
  simp_rw [htt]
  rw [Summable.tsum_add ((summable_weightedTerm_all 1 r).mul_left _)
    ((summable_weightedTerm_all phiPoly r).mul_left _), tsum_mul_left, tsum_mul_left]
  ring

theorem phi_even : Function.Even phi := by
  let f := fun r : ℝ => Real.exp (r/2) + 2*g r
  let v := fun r : ℝ => Real.exp (r/2)*(1/2)+2*thetaSeries (thetaStep 1) r
  have he (r : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (x/2)) (Real.exp (r/2)*(1/2)) r := by
    simpa using ((hasDerivAt_id r).div_const 2).exp
  have h1 : deriv f = v := funext fun r => ((he r).add ((thetaSeries_derivative 1 r).const_mul 2)).deriv
  have h2 (r : ℝ) : deriv v r = Real.exp (r/2)*(1/2)*(1/2) + 2*thetaSeries (thetaStep (thetaStep 1)) r :=
    (((he r).mul_const _).add ((thetaSeries_derivative (thetaStep 1) r).const_mul 2)).deriv
  have eq (r : ℝ) : 4*phi r = iteratedDeriv 2 f r - f r /4 := by
    rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one, h1, h2]
    dsimp [f]; linarith [ode_all r]
  have hfe : (fun x => f (-x)) = f := funext fullTheta_even
  intro r
  have h := iteratedDeriv_comp_neg 2 f r
  rw [hfe] at h
  norm_num at h
  linarith [eq (-r), eq r, show f (-r) = f r from fullTheta_even r]

theorem odd_jet (j : ℕ) (hj : Odd j) : p j 0 = 0 := by
  have h := iteratedDeriv_comp_neg j phi 0
  rw [show (fun x => phi (-x)) = phi from funext phi_even, p_iter] at h
  simp [hj.neg_one_pow] at h
  linarith

end GenesisTidalMellin
