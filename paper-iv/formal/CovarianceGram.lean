import data.real.basic
import tactic

/- Lean 3.51.1, mathlib3 65a1391a0106c9204fe45bc73a039f056558cb83.
   Algebraic components of the three-event and moment comparison. -/
namespace covariance_bounds

/-- A symmetric three-event correlation matrix with first-to-second entry
    r and both remaining off-diagonal entries c has this determinant. -/
theorem determinant_factor (r c : ℝ) :
  1 + 2*r*c^2 - r^2 - 2*c^2 = (1-r)*(1+r-2*c^2) := by ring

/-- A nonnegative determinant imposes the local bound when r < 1. -/
theorem three_event_bound (r c : ℝ) (hr : r < 1)
    (hd : 0 ≤ 1 + 2*r*c^2 - r^2 - 2*c^2) :
    2*c^2 ≤ 1 + r :=
begin
  rw [determinant_factor] at hd,
  by_contra h,
  have ht : 1+r-2*c^2 < 0 := by linarith,
  exact (not_lt_of_ge hd)
    (mul_neg_of_pos_of_neg (by linarith : 0 < 1-r) ht),
end

/-- Exact variance identity for a two-atom model of the magnitude. -/
theorem two_point_variance (p u v : ℝ) :
  p*u^2 + (1-p)*v^2 - (p*u+(1-p)*v)^2 =
    p*(1-p)*(u-v)^2 := by ring

/-- Distinct magnitudes with nondegenerate weights yield a strict gap. -/
theorem two_point_strict (p u v : ℝ) (hp : 0 < p) (hq : p < 1)
    (hne : u ≠ v) :
    (p*u+(1-p)*v)^2 < p*u^2 + (1-p)*v^2 :=
begin
  have hsq : 0 < (u-v)^2 := sq_pos_of_ne_zero (u-v) (sub_ne_zero.mpr hne),
  have hpos : 0 < p*(1-p)*(u-v)^2 :=
    mul_pos (mul_pos hp (by linarith)) hsq,
  linarith [two_point_variance p u v],
end

#print axioms determinant_factor
#print axioms three_event_bound
#print axioms two_point_variance
#print axioms two_point_strict
end covariance_bounds
