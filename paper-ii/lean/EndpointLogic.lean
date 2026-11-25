module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith

open Set
public section

namespace PaperIIAudit

/-- The exact root, strictly inside the certified bracket, and exclusion on its right. -/
theorem bracketRoot {p : ℝ → ℝ} {l h prev : ℝ} (order : l < h) (next : h ≤ prev)
    (continuity : ContinuousOn p (Icc l h)) (left : 0 < p l) (right : p h < 0)
    (derivative : ∀ x ∈ interior (Icc l h), deriv p x < 0)
    (before : ∀ x < l, 0 < p x) (after : ∀ x ∈ Icc h prev, p x < 0) :
    ∃ root ∈ Ioo l h, p root = 0 ∧ (∀ x < root, 0 < p x) ∧
      (∀ x ∈ Ioc root prev, p x < 0) := by
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' order.le continuity ⟨right.le, left.le⟩
  have anti := strictAntiOn_of_deriv_neg (convex_Icc l h) continuity derivative
  have lt₁ : l < t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
  have lt₂ : t < h := lt_of_le_of_ne ht.2 (by rintro rfl; linarith)
  refine ⟨t, ⟨lt₁, lt₂⟩, hz, ?_, ?_⟩
  · intro x hx
    by_cases b : x < l
    · exact before x b
    · have v := anti (show x ∈ Icc l h from ⟨le_of_not_gt b, hx.le.trans ht.2⟩) ht hx
      simpa [hz] using v
  · intro x hx
    by_cases b : x ≤ h
    · have v := anti ht (show x ∈ Icc l h from ⟨ht.1.trans hx.1.le, b⟩) hx.1
      simpa [hz] using v
    · exact after x ⟨(lt_of_not_ge b).le, hx.2⟩

/-- The exact-root version of the A/B/C argument of Theorem 5. -/
theorem threeRegions {q : ℝ → ℝ} (zero : q 0 = 0)
    (cont : ContinuousOn q (Icc 0 (1/16 : ℝ)))
    (A : ∀ x ∈ interior (Icc 0 (1/16 : ℝ)), 0 < deriv q x)
    (B : ∀ x ∈ Icc (1/16 : ℝ) (1/4), 0 < q x)
    (C : ∀ x ≥ (1/4 : ℝ), 0 < q x) : ∀ x > 0, 0 < q x := by
  intro x hx
  by_cases a : x ≤ 1/16
  · have m := strictMonoOn_of_deriv_pos (convex_Icc _ _) cont A
    have v := m (show (0 : ℝ) ∈ Icc 0 (1/16 : ℝ) from ⟨le_rfl, by norm_num⟩) ⟨hx.le, a⟩ hx
    simpa [zero] using v
  · by_cases b : x ≤ 1/4
    · exact B x ⟨(lt_of_not_ge a).le, b⟩
    · exact C x (lt_of_not_ge b).le

theorem exactEndpoint {A : Set ℝ} {t : ℝ} (necessity : A ⊆ Iic t)
    (atRoot : t ∈ A) (down : ∀ {x y : ℝ}, x ∈ A → y < x → y ∈ A) : A = Iic t := by
  apply Subset.antisymm necessity
  intro y hy
  rcases (show y ≤ t from hy).lt_or_eq with h | rfl
  · exact down atRoot h
  · exact atRoot

#print axioms bracketRoot
#print axioms threeRegions
#print axioms exactEndpoint
end PaperIIAudit
