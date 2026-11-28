import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Finset
namespace HeatMomentCertificate

def term (j : ℕ) (x : ℝ) := x^j / j.factorial
def rest (x : ℝ) := Real.exp x - ∑ j ∈ range 49, term j x

private theorem rest_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ rest x :=
  sub_nonneg.mpr (Real.sum_le_exp_of_nonneg hx 49)

private theorem rest_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : rest x ≤ rest y := by
  have series (v : ℝ) : HasSum (fun j => term j v) (Real.exp v) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have tail (v : ℝ) : HasSum (fun j : ℕ => term (j+49) v) (rest v) := by
    apply (hasSum_nat_add_iff (f := fun j => term j v) 49).2
    simpa [rest] using series v
  rw [← (tail x).tsum_eq, ← (tail y).tsum_eq]
  exact (tail x).summable.tsum_le_tsum (fun j => div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy _) (by positivity)) (tail y).summable

/-- For nonnegative arguments the exponential tail after degree 48 is
bounded by the full exponential at triple the argument, scaled by 3⁻⁴⁹. -/
theorem rest_le_triple {x : ℝ} (hx : 0 ≤ x) :
    rest x ≤ (1/(3:ℝ)^49) * Real.exp (3*x) := by
  have ser (v : ℝ) : HasSum (fun j => term j v) (Real.exp v) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have tail (v : ℝ) : HasSum (fun j : ℕ => term (j+49) v) (rest v) := by
    apply (hasSum_nat_add_iff (f := fun j => term j v) 49).2
    simpa [rest] using ser v
  have hscale (j : ℕ) : term (j+49) x ≤ (1/(3:ℝ)^49) * term (j+49) (3*x) := by
    unfold term
    rw [mul_pow]
    have hpow : (3:ℝ)^49 ≤ 3^(j+49) := pow_le_pow_right₀ (by norm_num) (by omega)
    have he : (1:ℝ) ≤ (1/3^49) * 3^(j+49) := by
      rw [one_div_mul_eq_div, le_div_iff₀ (by positivity), one_mul]
      exact hpow
    calc
      _ = 1 * (x^(j+49) / (j+49).factorial) := (one_mul _).symm
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right he (show 0 ≤ x^(j+49) / ((j+49).factorial : ℝ) by positivity) using 1 <;> ring
  have hsum := (tail x).summable.tsum_le_tsum hscale (((tail (3*x)).mul_left (1/3^49)).summable)
  rw [(tail x).tsum_eq, ((tail (3*x)).mul_left (1/3^49)).tsum_eq] at hsum
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sub_le_self _ (sum_nonneg fun j _ => div_nonneg (pow_nonneg (by positivity : 0 ≤ 3*x) _) (by positivity))

variable (μ : Measure ℝ) (w : ℝ → ℝ)
def moment (j : ℕ) := ∫ r, w r * term j (r^2) ∂μ
def errorMass := ∫ r, |w r| * rest (r^2) ∂μ

/-- Fixed, parameter-free enclosures of true integrals. -/
structure Bounds : Prop where
  constant : moment μ w 0 ≤ -(3/2000 : ℝ)
  linear : moment μ w 1 ≤ -1
  higher : ∑ k ∈ range 47, max (moment μ w (2+k)) 0 ≤ 3/4

theorem uniform_of_moments (hw : AEStronglyMeasurable w μ)
    (hdom : Integrable (fun r => |w r| * Real.exp (r^2)) μ)
    (h : Bounds μ w) (remainder : errorMass μ w ≤ 1/1000000) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ r, w r * Real.exp (s*r^2) ∂μ) ≤ -(1499/1000000 : ℝ) - s/4 := by
  have hv (r : ℝ) : s*r^2 ≤ r^2 := mul_le_of_le_one_left (sq_nonneg _) hs1
  have he (r : ℝ) : 0 ≤ rest (s*r^2) := rest_nonneg (mul_nonneg hs (sq_nonneg _))
  have hr (r : ℝ) : rest (r^2) ≤ Real.exp (r^2) := sub_le_self _ (sum_nonneg fun j _ =>
    div_nonneg (pow_nonneg (sq_nonneg _) _) (by positivity))
  have hm (j : ℕ) : Integrable (fun r => w r * term j (r^2)) μ := by
    apply hdom.mono' (hw.mul (by unfold term; fun_prop))
    filter_upwards with r
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ term j (r^2) by unfold term; positivity)]
    exact mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (sq_nonneg _) j) (abs_nonneg _)
  have herr : Integrable (fun r => |w r| * rest (r^2)) μ := by
    apply hdom.mono' (hw.norm.mul (by unfold rest term; fun_prop))
    filter_upwards with r
    change ‖|w r| * rest (r^2)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (rest_nonneg (sq_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (hr r) (abs_nonneg _)
  have point (r : ℝ) : w r * rest (s*r^2) ≤ |w r| * rest (r^2) :=
    mul_le_mul (le_abs_self _) (rest_mono (mul_nonneg hs (sq_nonneg _)) (hv r)) (he r) (abs_nonneg _)
  have hrem : Integrable (fun r => w r * rest (s*r^2)) μ := by
    apply hdom.mono' (hw.mul (by unfold rest term; fun_prop))
    filter_upwards with r
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (he r)]
    exact mul_le_mul_of_nonneg_left ((rest_mono (mul_nonneg hs (sq_nonneg _)) (hv r)).trans (hr r)) (abs_nonneg _)
  have split (r : ℝ) : w r * Real.exp (s*r^2) =
      (∑ j ∈ range 49, s^j * (w r * term j (r^2))) + w r * rest (s*r^2) := by
    unfold rest
    rw [mul_sub, mul_sum]
    have eq (j : ℕ) : w r * term j (s*r^2) = s^j * (w r * term j (r^2)) := by
      unfold term
      rw [mul_pow]
      ring
    simp_rw [eq]
    ring
  simp_rw [split]
  rw [integral_add (integrable_finsetSum _ fun j _ => (hm j).const_mul _) hrem,
    integral_finsetSum _ (fun j _ => (hm j).const_mul _)]
  simp_rw [integral_const_mul]
  change (∑ j ∈ range 49, s^j * moment μ w j) + _ < _
  have remUpper := (integral_mono hrem herr point).trans remainder
  rw [show 49 = 2 + 47 by decide, sum_range_add]
  have high (k : ℕ) : s^(2+k) * moment μ w (2+k) ≤ s * max (moment μ w (2+k)) 0 := by
    have hpow : s^(2+k) ≤ s^1 := pow_le_pow_of_le_one hs hs1 (by omega)
    exact (mul_le_mul_of_nonneg_left (le_max_left ..) (pow_nonneg hs _)).trans
      (mul_le_mul_of_nonneg_right (by simpa using hpow) (le_max_right ..))
  have upper := (sum_le_sum (fun k (_ : k ∈ range 47) => high k)).trans_eq
    (mul_sum _ _ _).symm
  have hc := h.constant
  have hl := mul_le_mul_of_nonneg_left h.linear hs
  have hh := mul_le_mul_of_nonneg_left h.higher hs
  rw [sum_range_succ (n := 1), sum_range_succ (n := 0)]
  simp only [sum_range_zero, zero_add, pow_zero, one_mul, pow_one]
  linarith

end HeatMomentCertificate
