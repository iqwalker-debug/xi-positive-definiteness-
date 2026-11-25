module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Tactic

public section

namespace PaperIIAudit
theorem heatDerivative {f : ℝ → ℝ} {x t : ℝ} {n : ℕ} (hf : ContDiffAt ℝ n f x) :
    iteratedDeriv n (fun s => f s * Real.exp (t*s)) x =
      Real.exp (t*x) * ∑ i ∈ Finset.range (n+1),
        (n.choose i : ℝ) * t^(n-i) * iteratedDeriv i f x := by
  have hg : ContDiffAt ℝ n (fun s => Real.exp (t*s)) x := by fun_prop
  rw [iteratedDeriv_fun_mul hf hg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_exp_const_mul]
  ring

/-- The differential inequality in the downward-closure lemma, at every finite order. -/
theorem heatDown {f : ℝ → ℝ} {x c : ℝ} {n : ℕ} (hf : ContDiffAt ℝ n f x)
    (hc : 0 ≤ c) (h : ∀ i ≤ n, 0 ≤ (-1 : ℝ)^i * iteratedDeriv i f x) :
    0 ≤ (-1 : ℝ)^n * iteratedDeriv n (fun s => f s * Real.exp ((-c)*s)) x := by
  rw [heatDerivative hf, mul_left_comm, Finset.mul_sum]
  apply mul_nonneg (Real.exp_pos _).le
  apply Finset.sum_nonneg
  intro i hi
  have ile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have sg : (-1 : ℝ)^n * (-c)^(n-i) = (-1 : ℝ)^i * c^(n-i) := by
    conv_lhs => lhs; rw [← Nat.add_sub_of_le ile, pow_add]
    rw [mul_assoc, ← mul_pow]
    simp
  calc
    0 ≤ (n.choose i : ℝ) * c^(n-i) * ((-1 : ℝ)^i * iteratedDeriv i f x) :=
      mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hc _)) (h i ile)
    _ = (n.choose i : ℝ) * ((-1 : ℝ)^n * (-c)^(n-i)) * iteratedDeriv i f x := by rw [sg]; ring
    _ = _ := by ring
#print axioms heatDerivative
#print axioms heatDown
end PaperIIAudit
