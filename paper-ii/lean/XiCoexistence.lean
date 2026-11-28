import XiCutoff

noncomputable section
open MeasureTheory Set
open GenesisTidalMellin
open scoped ENNReal

namespace XiCoexistence

abbrev E := GenesisD9Fourier.E
def density (u : ℝ) := profile 0 (u^2)
def weight (s u : ℝ) := Real.exp (s*u^2) * density u
def positiveWeight (s r : ℝ) := Real.exp (s*r^2) * phi r
def numerator (s t : ℝ) := 2 * ∫ r in Ioi (0:ℝ), positiveWeight s r * Real.cos (t*r)
def F (s t : ℝ) := numerator s t / numerator s 0
def A (d : ℕ) : Set ℝ := {s | GenesisFormalV4.RadialPSD (E d) (F s)}
/-- Complex-frequency cosine numerator. Division by a positive normalizer
does not affect its zero set. -/
def entireNumerator (s : ℝ) (z : ℂ) := ∫ u : ℝ, (weight s u : ℂ) * Complex.cos (z*u)
def B : Set ℝ := {s | ∀ z : ℂ, entireNumerator s z = 0 → z.im = 0}

private theorem phi_pos {r : ℝ} (hr : 0 ≤ r) : 0 < phi r := by
  have ht (n : ℕ) : 0 < weightedTerm phiPoly n r := by
    have hx : 3 < thetaX n r := by
      have hpow : (1:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n:ℝ)]
      have hex := Real.one_le_exp (show 0 ≤ 2*r by positivity)
      unfold thetaX
      nlinarith [mul_le_mul_of_nonneg_left hpow Real.pi_pos.le,
        mul_le_mul_of_nonneg_left hex (mul_nonneg Real.pi_pos.le (sq_nonneg ((n:ℝ)+1))),
        Real.pi_gt_three]
    unfold weightedTerm phiPoly
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    exact mul_pos (Real.exp_pos _) (mul_pos (by linarith) (by linarith))
  exact (summable_weightedTerm_all phiPoly r).tsum_pos (fun n => (ht n).le) 0 (ht 0)

theorem zero_profile : F 0 = GenesisTidal.criticalXiProfile := by
  funext t
  rw [amplitude_ratio]
  simp [F, numerator, positiveWeight, amplitude]

private theorem weight_int {s : ℝ} (hs : s ≤ 1) : IntegrableOn (positiveWeight s) (Ioi 0) := by
  let C := 16 * ∑' n : ℕ, Real.exp (-(n:ℝ))
  apply ((integrableOn_exp_neg_Ioi 0).const_mul C).mono'
  · have hc : Continuous phi := continuous_iff_continuousAt.mpr fun x =>
      (thetaSeries_derivative phiPoly x).continuousAt
    exact ((by fun_prop : Continuous (fun r : ℝ => Real.exp (s*r^2))).mul hc).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with r hr
  change 0 < r at hr
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2*r by positivity)
  have bound (n : ℕ) :
      ‖Real.exp (s*r^2) * weightedTerm phiPoly n r‖ ≤
        (16 * Real.exp (-r)) * Real.exp (-(n:ℝ)) := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
    have hsq : 1 ≤ ((n:ℝ)+1)^2 := by nlinarith [sq_nonneg (n:ℝ)]
    have hX : 3 * Real.exp (2*r) ≤ thetaX n r := by
      unfold thetaX
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le, Real.pi_gt_three]
    have hN : 3 * ((n:ℝ)+1)^2 ≤ thetaX n r := by
      unfold thetaX
      calc
        _ ≤ Real.pi * ((n:ℝ)+1)^2 := by gcongr; exact Real.pi_gt_three.le
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
    have bud : s*r^2 + 3*r/2 + n ≤ thetaX n r/2 := by
      nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg r), sq_nonneg (n:ℝ), sq_nonneg r]
    have hx : 3 ≤ thetaX n r := by linarith
    have hpoly := Real.pow_div_factorial_le_exp (thetaX n r/2) (by linarith : 0 ≤ thetaX n r/2) 2
    norm_num [Nat.factorial] at hpoly
    have hp : |phiPoly.eval (thetaX n r)| ≤ 16*Real.exp (thetaX n r/2) := by
      simp only [phiPoly, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub,
        Polynomial.eval_ofNat, abs_of_nonneg (mul_nonneg (by linarith : 0 ≤ thetaX n r)
          (by linarith : 0 ≤ 2*thetaX n r-3))]
      nlinarith
    simp only [weightedTerm, thetaTerm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (s*r^2) * (Real.exp (r/2-thetaX n r) * (16*Real.exp (thetaX n r/2))) := by gcongr
      _ = 16 * Real.exp (s*r^2 + (r/2-thetaX n r) + thetaX n r/2) := by rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ 16 * Real.exp (-r + -(n:ℝ)) := by gcongr; linarith
      _ = _ := by rw [Real.exp_add]; ring
  change ‖Real.exp (s*r^2) * ∑' n, weightedTerm phiPoly n r‖ ≤ _
  rw [← tsum_mul_left]
  exact (tsum_of_norm_bounded (Real.summable_exp_neg_nat.mul_left _).hasSum bound).trans_eq
    (by rw [tsum_mul_left]; dsimp [C]; ring)

private theorem mass_pos {s : ℝ} (hs : s ≤ 1) : 0 < numerator s 0 := by
  simp only [numerator, zero_mul, Real.cos_zero, mul_one]
  apply mul_pos (by norm_num)
  apply (setIntegral_pos_iff_support_of_nonneg_ae _ (weight_int hs)).mpr
  · rw [Set.inter_eq_right.mpr (show Ioi (0:ℝ) ⊆ Function.support (positiveWeight s) from
      fun r hr => (mul_pos (Real.exp_pos _) (phi_pos (le_of_lt hr))).ne')]
    exact isOpen_Ioi.measure_pos volume ⟨1, by norm_num⟩
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with r hr
    exact (mul_pos (Real.exp_pos _) (phi_pos (le_of_lt hr))).le

open GenesisD10Witness

def test (r : ℝ) : ℝ := (∑ k ∈ witnessPolynomial.support,
  (witnessPolynomial.coeff k : ℝ) * Real.cos ((7*Real.sqrt k)*r)) / normalization

/-- The parameter-uniform scalar inequality checked in certify_d10_heat.py
is enough to refute PSD, using the actual finite grid and coefficients. -/
theorem d10_failure {s : ℝ} (hs : s ≤ 1)
    (cert : (∫ r in Ioi (0:ℝ), positiveWeight s r * test r) < 0) : s ∉ A 10 := by
  let b (k : ℕ) (r : ℝ) := positiveWeight s r * Real.cos ((7*Real.sqrt k)*r)
  have hi (k) : IntegrableOn (b k) (Ioi 0) := (weight_int hs).mul_bdd (c := 1)
    (by fun_prop) (ae_of_all _ fun _ => Real.abs_cos_le_one _)
  have he (r : ℝ) : positiveWeight s r * test r =
      (∑ k ∈ witnessPolynomial.support, (witnessPolynomial.coeff k : ℝ) * b k r) / normalization := by
    simp only [test, mul_div_assoc', Finset.mul_sum, b]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he] at cert
  rw [integral_div, integral_finsetSum _ (fun k _ => (hi k).const_mul _)] at cert
  simp_rw [integral_const_mul] at cert
  have hn := (div_neg_iff_of_pos (show (0:ℝ) < normalization by exact_mod_cast normalization_pos)).mp cert
  apply not_radialPSD_of_negative
  change (∑ k ∈ witnessPolynomial.support, (witnessPolynomial.coeff k : ℝ) *
    ((2 * ∫ r in Ioi (0:ℝ), b k r) / numerator s 0)) < 0
  simp only [mul_div_assoc', ← Finset.sum_div]
  apply (div_neg_iff_of_pos (mass_pos hs)).mpr
  convert mul_neg_of_pos_of_neg (by norm_num : (0:ℝ) < 2) hn using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The derivative walk for the rational witness. The central value of a
radial density in nine dimensions does not affect its Fourier integral. -/
def jet : ℕ → ℝ → ℝ
  | 0 => fun x => Real.exp (x/16) * profile 0 x
  | j+1 => fun x => -(deriv (jet j) x) / Real.pi

structure WitnessBounds : Prop where
  measurable : ∀ j ≤ 4, Measurable (jet j)
  steps : ∀ j < 4, GenesisD9Fourier.OpenStep (jet j) (jet (j+1))
  fourth : ∀ x > 0, 0 < jet 4 x

theorem rational_D9 (h : WitnessBounds) : (1/16 : ℝ) ∈ A 9 := by
  have base := GenesisD9Fourier.base (G := jet 0) (F := numerator (1/16)) (by
    intro t _
    have point (r : ℝ) : jet 0 (r^2) * Real.cos (r*t) =
        positiveWeight (1/16) |r| * Real.cos (t*|r|) := by
      simp only [jet, profile, raw, p, Q, Real.sqrt_sq_eq_abs, positiveWeight, sq_abs, one_div_mul_eq_div]
      rcases le_or_gt 0 r with hr | hr
      · simp [abs_of_nonneg hr, mul_comm t]
      · simp [abs_of_neg hr, mul_comm t]
    simp_rw [point]
    exact integral_comp_abs (f := fun r => positiveWeight (1/16) r * Real.cos (t*r)))
  have hzpos := mass_pos (s := 1/16) (by norm_num)
  have hi : Integrable (fun k : E 1 => jet 0 (‖k‖^2)) := by
    by_contra hn
    have hz := base (0 : E 1)
    simp [GenesisD9Fourier.transform, integral_undef hn] at hz
    linarith
  have p3 := (h.steps 3 (by decide)).pos h.fourth
  have p2 := (h.steps 2 (by decide)).pos p3
  have p1 := (h.steps 1 (by decide)).pos p2
  have t1 := GenesisD9Fourier.lift_positive hi (h.measurable 1 (by decide)) p1 (h.steps 0 (by decide)) base
  have t2 := GenesisD9Fourier.lift_positive t1.1 (h.measurable 2 (by decide)) p2 (h.steps 1 (by decide)) t1.2
  have t3 := GenesisD9Fourier.lift_positive t2.1 (h.measurable 3 (by decide)) p3 (h.steps 2 (by decide)) t2.2
  have t4 := GenesisD9Fourier.lift_positive t3.1 (h.measurable 4 (by decide)) h.fourth (h.steps 3 (by decide)) t3.2
  let f := fun k : E 9 => if k = 0 then 0 else jet 4 (‖k‖^2) / numerator (1/16) 0
  have heq : f =ᵐ[volume] fun k => jet 4 (‖k‖^2) / numerator (1/16) 0 := by
    filter_upwards [volume.ae_ne (0 : E 9)] with k hk
    simp [f, hk]
  apply GenesisTidal.radialPSD_of_cosine_density f ((t4.1.div_const _).congr heq.symm)
  · intro k
    by_cases hk : k = 0
    · simp [f, hk]
    · simpa [f, hk] using (div_pos (h.fourth _ (sq_pos_of_pos (norm_pos_iff.mpr hk))) hzpos).le
  · intro x
    rw [F, ← t4.2 x, GenesisD9Fourier.transform, ← integral_div]
    apply integral_congr_ae
    filter_upwards [heq] with k hk
    rw [hk]
    ring

/-- An explicit positive D9 witness suffices. The paper's D9 endpoint
exceeds 1/16, and the published threshold bound is below 1/16. -/
theorem concreteCutoff {L : ℝ} (hL : 0 ≤ L) (hupper : L ≤ 0.22)
    (realZeros : B = Ici (L/4))
    (witnessBounds : WitnessBounds)
    (upper9 : A 9 ⊆ Iic 1)
    (cert : ∀ s ∈ Icc (0:ℝ) 1, (∫ r in Ioi (0:ℝ), positiveWeight s r * test r) < 0)
    {d : ℕ} (hd : 1 ≤ d) : (A d ∩ B).Nonempty ↔ d ≤ 9 := by
  have restrictDim {a b : ℕ} (hab : a ≤ b) {s : ℝ} (h : s ∈ A b) : s ∈ A a :=
    GenesisFormalV5.euclideanPSD_lower (F s) hab h
  constructor
  · rintro ⟨s, ha, hb⟩
    by_contra h
    rw [realZeros] at hb
    have hs : 0 ≤ s := le_trans (by positivity : 0 ≤ L/4) hb
    have ten := restrictDim (a := 10) (by omega) ha
    have capped : s ≤ 1 := upper9 (restrictDim (by decide : 9 ≤ 10) ten)
    exact d10_failure capped (cert s ⟨hs,capped⟩) ten
  · intro h
    refine ⟨1/16, restrictDim h (rational_D9 witnessBounds), ?_⟩
    rw [realZeros]
    change L/4 ≤ 1/16
    linarith

#print axioms zero_profile
#print axioms d10_failure
#print axioms rational_D9
#print axioms concreteCutoff
end XiCoexistence
