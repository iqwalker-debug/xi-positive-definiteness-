module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

public section

namespace PaperIIAudit
open Polynomial
noncomputable def unsignedP (a : ℕ → ℝ) (m : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (m+1), monomial k (a (m-k) / (k.factorial : ℝ))
noncomputable def endpointP (a : ℕ → ℝ) (m : ℕ) : Polynomial ℝ :=
  C ((-1 : ℝ)^m) * unsignedP a m

theorem derivativeUnsigned (a : ℕ → ℝ) (m : ℕ) :
    derivative (unsignedP a (m+1)) = unsignedP a m := by
  unfold unsignedP
  rw [derivative_sum, Finset.sum_range_succ']
  simp only [derivative_monomial_succ, Nat.succ_sub_succ_eq_sub, derivative_monomial,
    Nat.cast_zero, mul_zero, map_zero, add_zero]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem derivativeEndpoint (a : ℕ → ℝ) (m : ℕ) :
    derivative (endpointP a (m+1)) = -endpointP a m := by
  unfold endpointP
  rw [derivative_C_mul, derivativeUnsigned, pow_succ]
  simp
#print axioms derivativeEndpoint
end PaperIIAudit
