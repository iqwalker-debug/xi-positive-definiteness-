import ThetaJets
import PositiveWalk
import Mathlib.Tactic.IntervalCases
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace GenesisTidalMellin

private abbrev c : ℝ := 2*Real.pi

/-- The dimension profiles are written in inverse powers of the ordinary radius.
Their arbitrary central values will never enter a Lebesgue integral. -/
def raw : ℕ → ℝ → ℝ
  | 0, r => p 0 r
  | 1, r => ((-1:ℝ) * (p 1 r * r⁻¹^1)) / c^1
  | 2, r => ((1:ℝ) * (p 2 r * r⁻¹^2) + (-1:ℝ) * (p 1 r * r⁻¹^3)) / c^2
  | 3, r => ((-1:ℝ) * (p 3 r * r⁻¹^3) + (3:ℝ) * (p 2 r * r⁻¹^4) + (-3:ℝ) * (p 1 r * r⁻¹^5)) / c^3
  | 4, r => ((1:ℝ) * (p 4 r * r⁻¹^4) + (-6:ℝ) * (p 3 r * r⁻¹^5) + (15:ℝ) * (p 2 r * r⁻¹^6) + (-15:ℝ) * (p 1 r * r⁻¹^7)) / c^4
  | _+5, _ => 0

def profile (j : ℕ) (s : ℝ) := raw j (Real.sqrt s)

private theorem radius_deriv (j : ℕ) (hj : j < 4) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (raw j) (-c*r*raw (j+1) r) r := by
  have hi := (hasDerivAt_id r).inv hr.ne'
  have hc : c ≠ 0 := ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
  interval_cases j
  · convert (dp 0 r) using 1
    · rfl
    · simp only [raw, Nat.reduceAdd, Pi.pow_apply, Pi.inv_apply, id_eq]
      field_simp [hr.ne', hc] <;> ring_nf <;> field_simp [hr.ne', hc] <;> ring
  · convert ((((dp 1 r).mul (hi.pow 1)).const_mul (-1:ℝ)).div_const (c^1)) using 1
    · rfl
    · simp only [raw, Nat.reduceAdd, Pi.pow_apply, Pi.inv_apply, id_eq]
      field_simp [hr.ne', hc] <;> ring_nf <;> field_simp [hr.ne', hc] <;> ring
  · convert (((((dp 2 r).mul (hi.pow 2)).const_mul (1:ℝ)).add (((dp 1 r).mul (hi.pow 3)).const_mul (-1:ℝ))).div_const (c^2)) using 1
    · rfl
    · simp only [raw, Nat.reduceAdd, Pi.pow_apply, Pi.inv_apply, id_eq]
      field_simp [hr.ne', hc] <;> ring_nf <;> field_simp [hr.ne', hc] <;> ring
  · convert ((((((dp 3 r).mul (hi.pow 3)).const_mul (-1:ℝ)).add (((dp 2 r).mul (hi.pow 4)).const_mul (3:ℝ))).add (((dp 1 r).mul (hi.pow 5)).const_mul (-3:ℝ))).div_const (c^3)) using 1
    · rfl
    · simp only [raw, Nat.reduceAdd, Pi.pow_apply, Pi.inv_apply, id_eq]
      field_simp [hr.ne', hc] <;> ring_nf <;> field_simp [hr.ne', hc] <;> ring
theorem profile_meas (j : ℕ) (hj : j ≤ 4) : Measurable (profile j) := by
  have hp (i : ℕ) : Continuous (p i) := continuous_iff_continuousAt.mpr fun r => (dp i r).continuousAt
  have hm (i : ℕ) : Measurable (p i) := (hp i).measurable
  interval_cases j <;> unfold profile <;> simp only [raw] <;> fun_prop

theorem profile_openStep (j : ℕ) (hj : j < 4) : GenesisD9Fourier.OpenStep (profile j) (profile (j+1)) := by
  constructor
  · intro s hs
    have hr := Real.sqrt_pos.2 hs
    have h := (radius_deriv j hj hr).comp s (Real.hasDerivAt_sqrt hs.ne')
    convert h using 1
    · rfl
    · unfold profile c; field_simp [hr.ne'] <;> ring
  · apply Filter.Tendsto.comp (g := raw j) _ Real.tendsto_sqrt_atTop
    have hi : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    interval_cases j
    · exact p_decay 0
    · change Tendsto (fun r => raw 1 r) atTop (𝓝 0)
      simpa [raw] using (((p_decay 1).mul hi).const_mul (-1:ℝ)).div_const c
    · change Tendsto (fun r => raw 2 r) atTop (𝓝 0)
      simpa [raw] using ((((p_decay 2).mul (hi.pow 2)).const_mul (1:ℝ)).add (((p_decay 1).mul (hi.pow 3)).const_mul (-1:ℝ))).div_const (c^2)
    · change Tendsto (fun r => raw 3 r) atTop (𝓝 0)
      simpa [raw] using (((((p_decay 3).mul (hi.pow 3)).const_mul (-1:ℝ)).add (((p_decay 2).mul (hi.pow 4)).const_mul (3:ℝ))).add (((p_decay 1).mul (hi.pow 5)).const_mul (-3:ℝ))).div_const (c^3)
theorem profile_four_positive {r : ℝ} (hr : 0 < r)
    (h : 0 < r^3*p 4 r - 6*r^2*p 3 r + 15*r*p 2 r - 15*p 1 r) : 0 < raw 4 r := by
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hfactor : raw 4 r * (c^4 * r^7) = r^3*p 4 r - 6*r^2*p 3 r + 15*r*p 2 r - 15*p 1 r := by
    simp only [raw]
    field_simp [hc.ne', hr.ne']
    ring
  exact (mul_pos_iff_of_pos_right (mul_pos (pow_pos hc _) (pow_pos hr _))).mp (hfactor.symm ▸ h)

end GenesisTidalMellin
