import AxiomDraft
import ThetaCosine
import Mathlib.Probability.Moments.Variance

/-! Consequences of the spectral and numerical inputs for Papers I and II.
The hypotheses of the three application theorems record the external inputs. -/
noncomputable section
open MeasureTheory GenesisFormalV4 GenesisFormalV5 GenesisD10Witness
namespace XiHeat

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Admits (F : ℝ → ℝ) (d : ℕ) := RadialPSD (E d) F

def tilted (h r : ℝ) : ℝ := Real.exp (h*r^2) * GenesisTidalMellin.phi r
def profile (h t : ℝ) : ℝ := (∫ r : ℝ, Real.cos (t*r) * tilted h r) / ∫ r : ℝ, tilted h r

/-- The spectral input is a concrete marginal identity and a unit-mass radial density. -/
theorem cutoff_of_zero_marginal {F : ℝ → ℝ} {d : ℕ} (hd : Admits F d)
    (lift : Admits F (d+1) → ∃ g : ℝ → ℝ, Continuous g ∧
      Integrable (fun u : ℝ => g |u|) ∧ (∀ r ≥ 0, 0 ≤ g r) ∧
      (∫ x : E (d+1), g ‖x‖) = 1 ∧ (∫ u : ℝ, g |u|) = 0) :
    ∀ e, Admits F e ↔ e ≤ d := by
  apply euclideanPSD_cutoff F d hd
  intro hn
  obtain ⟨g, hc, hi, hg, hm, hz⟩ := lift hn
  have hex : ∃ x : E (d+1), g ‖x‖ ≠ 0 := by
    by_contra! hall
    simp [hall] at hm
  obtain ⟨x,hx⟩ := hex
  have hp := integral_pos_of_integrable_nonneg_nonzero (hc.comp continuous_abs) hi
    (fun u => hg |u| (abs_nonneg u)) (x := ‖x‖) (by simpa using hx)
  exact (ne_of_gt hp) hz

/-- Apply the marginal argument to an odd-dimensional endpoint root.
The scalar k absorbs the Fourier normalization and factorial. -/
theorem odd_endpoint_cutoff {m : ℕ} {hRoot k : ℝ} {P : ℝ → ℝ}
    (root : P hRoot = 0) (odd : Admits (profile hRoot) (2*m+1))
    (lift : Admits (profile hRoot) (2*m+1+1) → ∃ g : ℝ → ℝ, Continuous g ∧
      Integrable (fun u : ℝ => g |u|) ∧ (∀ r ≥ 0, 0 ≤ g r) ∧
      (∫ x : E (2*m+1+1), g ‖x‖) = 1 ∧ (∫ u : ℝ, g |u|) = k * P hRoot) :
    ∀ d, Admits (profile hRoot) d ↔ d ≤ 2*m+1 := by
  apply cutoff_of_zero_marginal odd
  simpa [root] using lift

/-- Taylor coefficients in ascending order; evaluation is Horner's rule. -/
def horner (h : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => a + h * horner h rest

private theorem horner_bound {h : ℝ} (hh : |h| ≤ 1/4) (cs : List ℝ)
    (boxes : ∀ a ∈ cs, |a| ≤ 5) : |horner h cs| ≤ 7 := by
  induction cs with
  | nil => norm_num [horner]
  | cons a cs ih =>
    have ha := boxes a (by simp)
    have ht := ih fun b hb => boxes b (by simp [hb])
    calc
      _ ≤ |a| + |h| * |horner h cs| := by simpa [horner, abs_mul] using abs_add_le a (h * horner h cs)
      _ ≤ 5 + (1/4 : ℝ) * 7 := by gcongr
      _ ≤ _ := by norm_num

/-- Rational majorant for the terms of order thirteen and above, valid on the whole window. -/
theorem tail_le_sq {h : ℝ} (hh : |h| ≤ 1/4) :
    10^11 * (|h|/3)^13 / (1-|h|/3) ≤ h^2 := by
  have hq : |h|/3 ≤ 1/12 := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ |h|/3) hq 11
  apply (div_le_iff₀ (by linarith : 0 < 1-|h|/3)).2
  calc
    _ = 10^11 * (|h|/3)^11 * (h^2/9) := by
      have hs : (|h|/3)^2 = h^2/9 := by norm_num [div_pow, sq_abs]
      rw [show (13:ℕ) = 11+2 by decide, pow_add, hs]
      ring
    _ ≤ 10^11 * (1/12 : ℝ)^11 * (h^2/9) := by gcongr
    _ ≤ h^2 * (1-|h|/3) := by nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hq)]

/-- The coarse coefficient boxes already suffice without subdividing the positive half-window. -/
theorem witness_envelope {h W a b : ℝ} {cs : List ℝ}
    (window : h ∈ Set.Icc (-1/1250 : ℝ) (1/4))
    (ha : a ≤ -1259/100000) (hb : b ∈ Set.Icc (-1513/100 : ℝ) (-1511/100))
    (boxes : ∀ v ∈ cs, |v| ≤ 5)
    (rem : W - horner h (a :: b :: cs) ≤ 10^11 * (|h|/3)^13 / (1-|h|/3)) :
    W < 0 := by
  obtain ⟨lo,hi⟩ := window
  obtain ⟨bl,bu⟩ := hb
  have hh : |h| ≤ 1/4 := abs_le.mpr ⟨by linarith,hi⟩
  have hs := (le_abs_self _).trans (horner_bound hh cs boxes)
  have hr := rem.trans (tail_le_sq hh)
  simp only [horner] at hr
  have major : W ≤ a + b*h + 8*h^2 := by nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hs)]
  by_cases pos : 0 ≤ h
  · nlinarith [mul_nonneg pos (sub_nonneg.mpr hi), mul_nonneg pos (sub_nonneg.mpr bu)]
  · have hn := le_of_not_ge pos
    nlinarith [mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr lo),
      mul_nonneg (neg_nonneg.mpr hn) (sub_nonneg.mpr bl)]

theorem heat_window_cutoff {h a b scale : ℝ} {cs : List ℝ}
    (window : h ∈ Set.Icc (-1/1250 : ℝ) (1/4)) (hs : 0 < scale)
    (nine : Admits (profile h) 9) (ha : a ≤ -1259/100000)
    (hb : b ∈ Set.Icc (-1513/100 : ℝ) (-1511/100)) (boxes : ∀ v ∈ cs, |v| ≤ 5)
    (rem : scale * compressed witnessPolynomial (sample (profile h)) - horner h (a :: b :: cs)
      ≤ 10^11 * (|h|/3)^13 / (1-|h|/3)) :
    ∀ d, Admits (profile h) d ↔ d ≤ 9 := by
  apply euclideanPSD_cutoff _ 9 nine
  apply not_radialPSD_of_negative
  exact neg_of_mul_neg_right (witness_envelope window ha hb boxes rem) hs.le

/-- A Gaussian scale mixture, normalized by its value at zero, has midpoint
ratio at most one. The mixing law is reweighted by its density at zero. -/
theorem mixture_midpoint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) {a b c : ℝ} (ha : 0 < a)
    (hb : b = a * ∫ x, X x ∂μ) (hc : c = a * ∫ x, (X x)^2 ∂μ) :
    b^2 ≤ a*c := by
  have hv := ProbabilityTheory.variance_nonneg X μ
  rw [ProbabilityTheory.variance_eq_sub hX] at hv
  change 0 ≤ (∫ x, (X x)^2 ∂μ) - (∫ x, X x ∂μ)^2 at hv
  rw [hb,hc]
  nlinarith [mul_nonneg (sq_nonneg a) hv]

theorem tilted_midpoint {h : ℝ}
    (gap : GenesisTidalMellin.phi 0 * GenesisTidalMellin.phi 1 <
      (GenesisTidalMellin.phi (Real.sqrt (1/2)))^2) :
    tilted h 0 * tilted h 1 < (tilted h (Real.sqrt (1/2)))^2 := by
  simp only [tilted, zero_pow (by decide : 2 ≠ 0), mul_zero, Real.exp_zero, one_mul,
    one_pow, mul_one, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [sq, ← Real.exp_add, show h*(1/2)+h*(1/2) = h by ring]
  nlinarith [mul_pos (Real.exp_pos h) (sub_pos.mpr gap)]

/-- Rational numerical input needed for the three true theta-series values. -/
structure MidpointBoxes : Prop where
  zero : GenesisTidalMellin.phi 0 ∈ Set.Icc (0 : ℝ) (1/2)
  mid : 1/1000 ≤ GenesisTidalMellin.phi (Real.sqrt (1/2))
  one : GenesisTidalMellin.phi 1 ≤ 1/5000000

theorem midpoint_gap (b : MidpointBoxes) :
    GenesisTidalMellin.phi 0 * GenesisTidalMellin.phi 1 <
      (GenesisTidalMellin.phi (Real.sqrt (1/2)))^2 := by
  have hu := mul_le_mul_of_nonneg_left b.one b.zero.1
  have hm := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/1000) b.mid 2
  linarith [b.zero.2]

/-- Three values of the Gaussian-mixture representation after reweighting by
the zero-radius density and pushing forward along the half-radius exponential. -/
def HasMidpointMixture (a b c : ℝ) : Prop := ∃ μ : Measure ℝ,
  IsProbabilityMeasure μ ∧ MemLp (fun x : ℝ => x) 2 μ ∧ 0 < a ∧
  b = a * ∫ x, x ∂μ ∧ c = a * ∫ x, x^2 ∂μ

/-- The concrete midpoint enclosure and Schoenberg implication remain explicit premises. -/
theorem finite_ceiling (h : ℝ) (one : Admits (profile h) 1)
    (boxes : MidpointBoxes)
    (mixture : (∀ d, Admits (profile h) d) →
      HasMidpointMixture (tilted h 0) (tilted h (Real.sqrt (1/2))) (tilted h 1)) :
    ∃ D ≥ 1, ∀ d, Admits (profile h) d ↔ d ≤ D := by
  classical
  have fails : ∃ d, ¬ Admits (profile h) d := by
    by_contra! hall
    obtain ⟨μ,hm,hX,ha,hb,hc⟩ := mixture hall
    let _ := hm
    exact (not_lt_of_ge (mixture_midpoint μ hX ha hb hc)) (tilted_midpoint (midpoint_gap boxes))
  let n := Nat.find fails
  have hn : ¬ Admits (profile h) n := Nat.find_spec fails
  have hn2 : 1 < n := by
    by_contra! hle
    exact hn (euclideanPSD_lower _ hle one)
  have hd : Admits (profile h) (n-1) := by
    by_contra hf
    have hmin : n ≤ n-1 := Nat.find_min' fails hf
    omega
  have hs : n - 1 + 1 = n := by omega
  apply Exists.intro (n-1)
  refine ⟨by omega, euclideanPSD_cutoff _ _ hd ?_⟩
  rw [hs]
  exact hn

#print axioms cutoff_of_zero_marginal
#print axioms odd_endpoint_cutoff
#print axioms midpoint_gap
#print axioms tail_le_sq
#print axioms witness_envelope
#print axioms heat_window_cutoff
#print axioms mixture_midpoint
#print axioms tilted_midpoint
#print axioms finite_ceiling
end XiHeat
