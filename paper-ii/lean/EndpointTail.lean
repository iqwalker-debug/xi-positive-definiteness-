module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

public section

namespace PaperIIAudit
/-- For a majorant with successive ratio at most 1/2, the entire tail
is at most twice its initial term. The coefficient bound is a hypothesis. -/
theorem tailFactorTwo {a b : ℕ → ℝ} (pos : ∀ n, 0 ≤ a n) (dom : ∀ n, a n ≤ b n)
    (ratio : ∀ n, b (n+1) ≤ b n * (1/2 : ℝ)) :
    Summable a ∧ (∑' n, a n) ≤ 2 * b 0 := by
  have hdom (n : ℕ) : b n ≤ b 0 * (1/2 : ℝ)^n := by
    induction n with
    | zero => simp
    | succ k ih =>
      calc
        b (k+1) ≤ b k * (1/2) := ratio k
        _ ≤ (b 0 * (1/2 : ℝ)^k) * (1/2) := by gcongr
        _ = _ := by rw [pow_succ]; ring
  have geo := summable_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)
  have major := geo.mul_left (b 0)
  have leq := fun n => (dom n).trans (hdom n)
  have sa : Summable a := .of_nonneg_of_le pos leq major
  refine ⟨sa, (sa.tsum_le_tsum leq major).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  ring
#print axioms tailFactorTwo
end PaperIIAudit
