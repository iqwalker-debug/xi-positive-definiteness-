import AxiomDraft
import D9Coverage
import XiProfile

noncomputable section
open MeasureTheory Set Filter Polynomial
open scoped Topology InnerProductSpace
namespace GenesisTidalMellin

def N (r : ℝ) : ℝ := r^3*p 4 r - 6*r^2*p 3 r + 15*r*p 2 r - 15*p 1 r

private theorem Q_signs {x : ℝ} (hx : 20 ≤ x) :
    (Q 1).eval x < 0 ∧ 0 < (Q 2).eval x ∧ (Q 3).eval x < 0 ∧ 0 < (Q 4).eval x := by
  have h := GenesisTidal.d9_shifted_polynomial_signs hx
  refine ⟨?_,?_,?_,?_⟩
  · convert h.1 using 1 <;> norm_num [Q, thetaStep, phiPoly, Polynomial.derivative_mul] <;> ring
  · convert h.2.1 using 1 <;> norm_num [Q, thetaStep, phiPoly, Polynomial.derivative_mul] <;> ring
  · convert h.2.2.1 using 1 <;> norm_num [Q, thetaStep, phiPoly, Polynomial.derivative_mul] <;> ring
  · convert h.2.2.2 using 1 <;> norm_num [Q, thetaStep, phiPoly, Polynomial.derivative_mul] <;> ring

private theorem far {r : ℝ} (hr : 1 ≤ r) : 0 < N r := by
  have hx (n : ℕ) := Q_signs (GenesisTidal.d9_theta_argument_gt_twenty hr n).le
  have pos (j : ℕ) (hv : ∀ n, 0 < (Q j).eval (thetaX n r)) : 0 < p j r :=
    (summable_weightedTerm_all (Q j) r).tsum_pos
      (fun n => (mul_pos (Real.exp_pos _) (hv n)).le) 0 (mul_pos (Real.exp_pos _) (hv 0))
  have neg (j : ℕ) (hv : ∀ n, (Q j).eval (thetaX n r) < 0) : p j r < 0 := by
    have hh (n : ℕ) : weightedTerm (Q j) n r < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) (hv n)
    have hh' := (summable_weightedTerm_all (Q j) r).neg.tsum_pos
      (fun n => (neg_pos.mpr (hh n)).le) 0 (neg_pos.mpr (hh 0))
    simpa [p,thetaSeries,tsum_neg] using hh'
  have h1 := neg 1 fun n => (hx n).1
  have h2 := pos 2 fun n => (hx n).2.1
  have h3 := neg 3 fun n => (hx n).2.2.1
  have h4 := pos 4 fun n => (hx n).2.2.2
  have hp : 0 < r := by linarith
  unfold N
  have ha := mul_pos (pow_pos hp 3) h4
  have hb := mul_neg_of_pos_of_neg (mul_pos (by norm_num : (0:ℝ)<6) (pow_pos hp 2)) h3
  have hc := mul_pos (mul_pos (by norm_num : (0:ℝ)<15) hp) h2
  linarith

theorem numerator_positive
    (h8 : GenesisD9Coverage.Sound 320 (p 8) GenesisD9Coverage.near256)
    (hm : GenesisD9Coverage.Sound 320 N GenesisD9Coverage.middle256) :
    ∀ r > 0, 0 < N r := by
  intro r hr
  by_cases ha : r ≤ 1/5
  · apply GenesisD9Fourier.near_numerator_pos p (b := 1/5)
      (fun j _ => continuous_iff_continuousAt.mpr fun t => (dp j t).continuousAt)
      (fun j _ => dp j) (odd_jet 1 (by decide)) (odd_jet 3 (by decide))
      (odd_jet 5 (by decide)) (odd_jet 7 (by decide)) _ r ⟨hr,ha⟩
    exact fun t ht => GenesisD9Coverage.near_positive h8 t ⟨ht.1.le,ht.2.le⟩
  by_cases hb : r ≤ 1
  · exact GenesisD9Coverage.middle_positive hm r ⟨le_of_not_ge ha,hb⟩
  · exact far (le_of_not_ge hb)

def amplitude (t : ℝ) : ℝ := 2 * ∫ r in Ioi (0:ℝ), phi r * Real.cos (t*r)

theorem amplitude_base (t : ℝ) :
    (∫ s : ℝ, profile 0 (s^2) * Real.cos (s*t)) = amplitude t := by
  have eq (s : ℝ) : profile 0 (s^2) * Real.cos (s*t) =
      phi |s| * Real.cos (t*|s|) := by
    simp only [profile,raw,p,Q,Real.sqrt_sq_eq_abs]
    rcases le_or_gt 0 s with hs | hs
    · simp [abs_of_nonneg hs, mul_comm]
    · simp [abs_of_neg hs, mul_neg, mul_comm]
  simp_rw [eq]
  exact integral_comp_abs (f := fun s => phi s * Real.cos (t*s))

theorem amplitude_ratio (t : ℝ) : GenesisTidal.criticalXiProfile t = amplitude t / amplitude 0 := by
  have ht (u : ℝ) : GenesisTidal.completedXi (criticalPoint u) = ((2*amplitude u:ℝ):ℂ) := by
    rw [amplitude, show ∀ a : ℝ, 2 * (2*a) = 4*a from fun a => by ring]
    exact completedXi_eq_phi_cosine u
  unfold GenesisTidal.criticalXiProfile
  change (GenesisTidal.completedXi (criticalPoint t) / GenesisTidal.completedXi (1/2)).re = _
  rw [← show criticalPoint 0 = (1/2:ℂ) by simp [criticalPoint], ht, ht, ← Complex.ofReal_div,
    Complex.ofReal_re]
  by_cases h : amplitude 0 = 0
  · simp [h]
  · field_simp

theorem d9_density_of_positive_numerator (hN : ∀ r > 0, 0 < N r) :
    ∃ f : GenesisD9Fourier.E 9 → ℝ, Integrable f ∧
      (∀ k, 0 ≤ f k) ∧ (∀ k ≠ 0, 0 < f k) ∧
      (∀ x : GenesisD9Fourier.E 9,
        GenesisTidal.criticalXiProfile ‖x‖ = ∫ k, f k * Real.cos ⟪k,x⟫_ℝ) := by
  have h4 {s : ℝ} (hs : 0 < s) : 0 < profile 4 s :=
    profile_four_positive (Real.sqrt_pos.2 hs) (hN _ (Real.sqrt_pos.2 hs))
  have h3 := (profile_openStep 3 (by decide)).pos (fun _ hs => h4 hs)
  have h2 := (profile_openStep 2 (by decide)).pos h3
  have h1 := (profile_openStep 1 (by decide)).pos h2
  have h0 := (profile_openStep 0 (by decide)).pos h1
  have hp (r : ℝ) (hr : 0 < r) : 0 < phi r := by
    simpa [profile,raw,p,Q,Real.sqrt_sq hr.le] using h0 (r^2) (pow_pos hr 2)
  have hZ : 0 < amplitude 0 := by
    simp only [amplitude, zero_mul, Real.cos_zero, mul_one]
    apply mul_pos (by norm_num)
    apply (setIntegral_pos_iff_support_of_nonneg_ae _
      (thetaSeries_integrableOn phiPoly)).mpr
    · have he : Function.support phi ∩ Ioi 0 = Ioi 0 :=
        Set.inter_eq_right.mpr (fun r hr => (hp r hr).ne')
      rw [he]
      exact isOpen_Ioi.measure_pos volume ⟨1, by norm_num⟩
    · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with r hr
      exact (hp r hr).le
  have hb := GenesisD9Fourier.base (fun t _ => amplitude_base t)
  have hi : Integrable (fun k : GenesisD9Fourier.E 1 => profile 0 (‖k‖^2)) := by
    by_contra h
    have hz := hb (0 : GenesisD9Fourier.E 1)
    simp [GenesisD9Fourier.transform, integral_undef h] at hz
    linarith
  have t1 := GenesisD9Fourier.lift_positive hi (profile_meas 1 (by decide)) h1 (profile_openStep 0 (by decide)) hb
  have t2 := GenesisD9Fourier.lift_positive t1.1 (profile_meas 2 (by decide)) h2 (profile_openStep 1 (by decide)) t1.2
  have t3 := GenesisD9Fourier.lift_positive t2.1 (profile_meas 3 (by decide)) h3 (profile_openStep 2 (by decide)) t2.2
  have t4 := GenesisD9Fourier.lift_positive t3.1 (profile_meas 4 (by decide)) (fun _ hs => h4 hs)
    (profile_openStep 3 (by decide)) t3.2
  refine ⟨fun k => profile 4 (‖k‖^2) / amplitude 0, t4.1.div_const _, ?_, ?_, ?_⟩
  · intro k
    apply div_nonneg _ hZ.le
    rcases eq_or_ne k 0 with rfl | hk
    · simp [profile,raw]
    · exact (h4 (sq_pos_of_pos (norm_pos_iff.mpr hk))).le
  · exact fun k hk => div_pos (h4 (sq_pos_of_pos (norm_pos_iff.mpr hk))) hZ
  · intro x
    rw [amplitude_ratio, ← t4.2 x, GenesisD9Fourier.transform, ← integral_div]
    apply integral_congr_ae
    filter_upwards with k
    ring

theorem d9_of_arb_cells
    (h8 : GenesisD9Coverage.Sound 320 (p 8) GenesisD9Coverage.near256)
    (hm : GenesisD9Coverage.Sound 320 N GenesisD9Coverage.middle256) :
    GenesisFormalV4.RadialPSD (GenesisD9Fourier.E 9) GenesisTidal.criticalXiProfile := by
  obtain ⟨f, hf, hn, _, hinv⟩ := d9_density_of_positive_numerator (numerator_positive h8 hm)
  exact GenesisTidal.radialPSD_of_cosine_density f hf hn hinv

/-- Earlier form of the cutoff, kept as a cross-check: its external inputs are
the two D9 Arb tables and the two aggregate D10 bounds. The D9 tables are no
longer needed; see `exact_cutoff_of_row_bounds` in `XiStrict.lean`, whose only
external inputs are the D10 row enclosures. -/
theorem exact_cutoff_of_arb
    (h8 : GenesisD9Coverage.Sound 320 (p 8) GenesisD9Coverage.near256)
    (hm : GenesisD9Coverage.Sound 320 N GenesisD9Coverage.middle256)
    (hret : GenesisD10Witness.retained GenesisTidal.criticalXiProfile ≤ -(125963671 : ℝ)/10000000000)
    (hom : GenesisD10Witness.omitted GenesisTidal.criticalXiProfile ≤ (1 : ℝ)/1000000000)
    (d : ℕ) :
    GenesisFormalV4.RadialPSD (GenesisD9Fourier.E d) GenesisTidal.criticalXiProfile ↔ d ≤ 9 :=
  GenesisTidal.criticalXi_cutoff_of_boundary_dimensions (d9_of_arb_cells h8 hm)
    (GenesisD10Witness.xi_not_radialPSD_d10_of_enclosures hret hom) d

end GenesisTidalMellin
#print axioms GenesisTidalMellin.exact_cutoff_of_arb
