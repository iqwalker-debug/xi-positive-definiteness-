import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Push

noncomputable section

open MeasureTheory Set Complex HurwitzZeta

namespace GenesisTidalMellin

def centralThetaPair : WeakFEPair ℂ := hurwitzEvenFEPair 0

def criticalPoint (t : ℝ) : ℂ := 1 / 2 + (t : ℂ) * I

def splitTheta (r : ℝ) : ℂ :=
  (Real.exp (r / 2) : ℂ) * centralThetaPair.f_modif (Real.exp (2 * r))

/-- Logarithmic substitution for the exact pole-subtracted completed zeta.
The factor two from the substitution cancels the FE pair's normalization. -/
theorem completedZeta₀_critical_eq_exp_integral (t : ℝ) :
    completedRiemannZeta₀ (criticalPoint t) =
      ∫ r : ℝ, Complex.exp (((t * r : ℝ) : ℂ) * I) * splitTheta r := by
  let s := criticalPoint t / 2
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * centralThetaPair.f_modif x
  let h : ℝ → ℂ := fun x => Real.exp x • f (Real.exp x)
  change (∫ x in Ioi (0 : ℝ), f x) / 2 = _
  rw [← MeasureTheory.integral_comp_exp f]
  change (∫ x, h x) / 2 = _
  have hs : (∫ r : ℝ, h (2 * r)) = (∫ x, h x) / 2 := by
    rw [Measure.integral_comp_mul_left]
    norm_num [div_eq_mul_inv, real_smul]
    ring
  rw [← hs]
  apply integral_congr_ae
  filter_upwards with r
  have hp := Real.exp_pos (2 * r)
  have hn : ((Real.exp (2 * r) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  dsimp [h, f, splitTheta]
  rw [cpow_def_of_ne_zero hn, ← ofReal_log hp.le, Real.log_exp]
  simp only [ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  dsimp [s, criticalPoint]
  push_cast
  ring

/-- This is the actual theta series used in the certificate, before differentiation. -/
theorem splitTheta_pos_eq_tsum {r : ℝ} (hr : 0 < r) :
    splitTheta r =
      (2 * (∑' n : ℕ, Real.exp (r / 2 -
        Real.pi * ((n : ℝ) + 1)^2 * Real.exp (2 * r))) : ℝ) := by
  have he : 1 < Real.exp (2 * r) := Real.one_lt_exp_iff.mpr (by linarith)
  have htheta := (hasSum_nat_cosKernel₀ 0 (Real.exp_pos (2 * r))).tsum_eq
  have htheta' : (∑' n : ℕ, 2 * Real.exp
      (-Real.pi * ((n : ℝ) + 1)^2 * Real.exp (2 * r))) =
      evenKernel 0 (Real.exp (2 * r)) - 1 := by
    simpa [evenKernel_eq_cosKernel_of_zero] using htheta
  simp only [splitTheta, centralThetaPair, WeakFEPair.f_modif, Pi.add_apply,
    indicator_of_mem (mem_Ioi.mpr he), indicator_of_notMem (notMem_Ioo_of_ge he.le),
    add_zero, hurwitzEvenFEPair, Function.comp_apply, ite_true, ← ofReal_one,
    ← ofReal_sub, ← ofReal_mul]
  exact_mod_cast (calc
    Real.exp (r / 2) * (evenKernel 0 (Real.exp (2 * r)) - 1) =
      Real.exp (r / 2) * (∑' n : ℕ, 2 * Real.exp
        (-Real.pi * ((n : ℝ) + 1)^2 * Real.exp (2 * r))) := by rw [htheta']
    _ = 2 * (∑' n : ℕ, Real.exp (r / 2 -
        Real.pi * ((n : ℝ) + 1)^2 * Real.exp (2 * r))) := by
      simp_rw [← tsum_mul_left, sub_eq_add_neg, Real.exp_add]
      apply tsum_congr
      intro n
      ring)

end GenesisTidalMellin

#print axioms GenesisTidalMellin.completedZeta₀_critical_eq_exp_integral
#print axioms GenesisTidalMellin.splitTheta_pos_eq_tsum

open Filter
open scoped Topology

namespace GenesisTidalMellin

/-- Twice integrating by parts in one FTC step. For the actual theta function
the endpoint is −1/4. Regularity and decay remain explicit obligations. -/
theorem theta_cosine_ibp (t : ℝ) (g g' g'' phi : ℝ → ℝ)
    (hg : ∀ r ≥ 0, HasDerivAt g (g' r) r)
    (hgg : ∀ r ≥ 0, HasDerivAt g' (g'' r) r)
    (hphi : ∀ r > 0, g'' r - g r / 4 = 2 * phi r)
    (hend : g' 0 = -1 / 4)
    (hdecay : Tendsto (fun r => g' r * Real.cos (t*r) + t*g r * Real.sin (t*r))
      atTop (𝓝 0))
    (hi : IntegrableOn (fun r => phi r * Real.cos (t*r)) (Ioi 0))
    (hj : IntegrableOn (fun r => g r * Real.cos (t*r)) (Ioi 0)) :
    4 * (∫ r in Ioi (0 : ℝ), phi r * Real.cos (t*r)) =
      1 / 2 - 2 * (t^2 + 1/4) * (∫ r in Ioi (0 : ℝ), g r * Real.cos (t*r)) := by
  let H : ℝ → ℝ := fun r => 2 * (phi r * Real.cos (t*r)) +
    (t^2 + 1/4) * (g r * Real.cos (t*r))
  have hH : IntegrableOn H (Ioi 0) := (hi.const_mul 2).add (hj.const_mul _)
  have hd : ∀ r ∈ Ioi (0 : ℝ),
      HasDerivAt (fun r => g' r * Real.cos (t*r) + t*g r * Real.sin (t*r)) (H r) r := by
    intro r hr
    have hr' : 0 < r := hr
    have ht : HasDerivAt (fun x : ℝ => t*x) t r := by
      simpa using (hasDerivAt_id r).const_mul t
    have h := ((hgg r hr'.le).mul ht.cos).add (((hg r hr'.le).const_mul t).mul ht.sin)
    convert h using 1
    dsimp [H]
    linear_combination - Real.cos (t*r) * hphi r hr'
  have hc : ContinuousWithinAt
      (fun r => g' r * Real.cos (t*r) + t*g r * Real.sin (t*r)) (Ici 0) 0 :=
    (((hgg 0 le_rfl).continuousAt.mul (by fun_prop)).add
      (((hg 0 le_rfl).continuousAt.const_mul t).mul (by fun_prop))).continuousWithinAt
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc hd hH hdecay
  change (∫ r in Ioi (0 : ℝ), 2 * (phi r * Real.cos (t*r)) +
    (t^2+1/4) * (g r * Real.cos (t*r))) = _ at h
  rw [integral_add (hi.const_mul _) (hj.const_mul _), integral_const_mul, integral_const_mul] at h
  simp [hend] at h
  linarith

end GenesisTidalMellin

#print axioms GenesisTidalMellin.theta_cosine_ibp

namespace GenesisTidalMellin

theorem splitTheta_even : Function.Even splitTheta := by
  intro r
  have hp := Real.exp_pos (2 * r)
  have hg : centralThetaPair.g_modif = centralThetaPair.f_modif := by
    simp [centralThetaPair, WeakFEPair.g_modif, WeakFEPair.f_modif,
      hurwitzEvenFEPair, evenKernel_eq_cosKernel_of_zero]
  have hFE : centralThetaPair.f_modif (1 / Real.exp (2 * r)) =
      ((Real.exp (2 * r) ^ (1/2 : ℝ) : ℝ) : ℂ) *
      centralThetaPair.f_modif (Real.exp (2 * r)) := by
    have h := centralThetaPair.hf_modif_FE _ hp
    rw [hg] at h
    simpa [centralThetaPair, hurwitzEvenFEPair, smul_eq_mul] using h
  have hm : Real.exp (2 * (-r)) = 1 / Real.exp (2 * r) := by
    rw [mul_neg, Real.exp_neg, one_div]
  rw [splitTheta, splitTheta, hm, hFE,
    Real.rpow_def_of_pos hp, Real.log_exp, ← mul_assoc, ← ofReal_mul, ← Real.exp_add]
  congr 3
  ring

/-- Exact critical-line identity for the same completed Xi expression used
by the cutoff theorem. The density in this formula is the undifferentiated
split theta, not the eventual D1 or D9 density. -/
theorem completedXi_critical_eq_splitTheta (t : ℝ) :
    (criticalPoint t * (criticalPoint t - 1) * completedRiemannZeta₀ (criticalPoint t) + 1) / 2 =
    1 / 2 - (((t^2 + 1/4 : ℝ) : ℂ) / 2) *
      (∫ r : ℝ, Complex.exp (((t * r : ℝ) : ℂ) * I) * splitTheta r) := by
  rw [completedZeta₀_critical_eq_exp_integral]
  have h : criticalPoint t * (criticalPoint t - 1) = -((t^2 + 1/4 : ℝ) : ℂ) := by
    unfold criticalPoint
    push_cast
    linear_combination ((t : ℂ)^2) * Complex.I_sq
  rw [h]
  ring

end GenesisTidalMellin

#print axioms GenesisTidalMellin.splitTheta_even
#print axioms GenesisTidalMellin.completedXi_critical_eq_splitTheta

namespace GenesisTidalMellin

def thetaX (n : ℕ) (r : ℝ) : ℝ :=
  Real.pi * ((n : ℝ) + 1)^2 * Real.exp (2*r)

def thetaTerm (n : ℕ) (r : ℝ) : ℝ :=
  Real.exp (r/2 - thetaX n r)

theorem hasDerivAt_thetaX (n : ℕ) (r : ℝ) :
    HasDerivAt (thetaX n) (2 * thetaX n r) r := by
  have h : HasDerivAt (fun x : ℝ => 2*x) 2 r := by
    simpa using (hasDerivAt_id r).const_mul 2
  convert h.exp.const_mul (Real.pi * ((n : ℝ) + 1)^2) using 1
  · rfl
  · unfold thetaX
    ring

theorem hasDerivAt_thetaTerm (n : ℕ) (r : ℝ) :
    HasDerivAt (thetaTerm n) (thetaTerm n r * (1/2 - 2 * thetaX n r)) r := by
  have h : HasDerivAt (fun x : ℝ => x/2) (1/2) r := by
    simpa using (hasDerivAt_id r).div_const 2
  exact (h.sub (hasDerivAt_thetaX n r)).exp

/-- Per summand, the second derivative minus one fourth of the summand
is twice the exact theta term used by the Arb certificate. -/
theorem hasDerivAt_thetaTerm_first (n : ℕ) (r : ℝ) :
    HasDerivAt (fun u => thetaTerm n u * (1/2 - 2 * thetaX n u))
      (thetaTerm n r / 4 +
        2 * (thetaTerm n r * thetaX n r * (2 * thetaX n r - 3))) r := by
  have h := (hasDerivAt_thetaTerm n r).mul
    ((hasDerivAt_thetaX n r).const_mul 2 |>.const_sub (1/2))
  convert h using 1 <;> ring

end GenesisTidalMellin

#print axioms GenesisTidalMellin.hasDerivAt_thetaTerm_first
