import XiCutoff
import EndpointHeat
import HeatMomentCertificate

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open GenesisTidalMellin

namespace XiCoexistence

abbrev E := GenesisD9Fourier.E
def positiveWeight (s r : ℝ) := Real.exp (s*r^2) * phi r
def numerator (s t : ℝ) := 2 * ∫ r in Ioi (0:ℝ), positiveWeight s r * Real.cos (t*r)
def F (s t : ℝ) := numerator s t / numerator s 0
def A (d : ℕ) : Set ℝ := {s | GenesisFormalV4.RadialPSD (E d) (F s)}
/-- Complex-frequency cosine numerator. Division by a positive normalizer
does not affect its zero set. -/
def entireNumerator (s : ℝ) (z : ℂ) :=
  2 * ∫ r in Ioi (0:ℝ), (positiveWeight s r : ℂ) * Complex.cos (z*r)
def B : Set ℝ := {s | ∀ z : ℂ, entireNumerator s z = 0 → z.im = 0}

theorem entire_on_real (s t : ℝ) : entireNumerator s (t : ℂ) = (numerator s t : ℂ) := by
  have hp (r : ℝ) : (positiveWeight s r : ℂ) * Complex.cos ((t:ℂ)*r) =
      ((positiveWeight s r * Real.cos (t*r) : ℝ) : ℂ) := by push_cast; rfl
  unfold entireNumerator numerator
  simp_rw [hp, integral_complex_ofReal]
  push_cast; rfl

def newmanH (t : ℝ) (z : ℂ) :=
  ∫ u in Ioi (0:ℝ), ((Real.exp (t*u^2) * phi (2*u) : ℝ) : ℂ) * Complex.cos (z*u)

theorem heatScaling (s : ℝ) (z : ℂ) : entireNumerator s z = 4 * newmanH (4*s) (2*z) := by
  let g (r : ℝ) := (positiveWeight s r : ℂ) * Complex.cos (z*r)
  have h := integral_comp_mul_left_Ioi' g 0 (by norm_num : (0:ℝ) < 2)
  rw [mul_zero, Complex.real_smul] at h
  change 2 * (∫ r in Ioi (0:ℝ), g r) = _
  rw [← h]
  have hp (u : ℝ) : g (2*u) =
      ((Real.exp ((4*s)*u^2) * phi (2*u) : ℝ) : ℂ) * Complex.cos ((2*z)*u) := by
    simp only [g, positiveWeight, show s*(2*u)^2 = (4*s)*u^2 by ring,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [show z*(2*(u:ℂ)) = (2*z)*u by ring]
  simp_rw [hp]
  unfold newmanH
  push_cast
  ring

theorem zeroThreshold (L : ℝ)
    (deBruijnNewman : ∀ t, (∀ z : ℂ, newmanH t z = 0 → z.im = 0) ↔ L ≤ t) :
    B = Ici (L/4) := by
  ext s
  change (∀ z : ℂ, entireNumerator s z = 0 → z.im = 0) ↔ L/4 ≤ s
  constructor
  · intro hs
    have h : L ≤ 4*s := (deBruijnNewman _).mp (by
      intro z hz
      have hzero := hs (z/2) (by rw [heatScaling, show 2*(z/2) = z by ring, hz, mul_zero])
      simpa using hzero)
    linarith
  · intro hs z hz
    rw [heatScaling, mul_eq_zero] at hz
    have hzero := (deBruijnNewman (4*s)).mpr (by linarith) (2*z)
      (hz.resolve_left (by norm_num))
    simpa using hzero

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

private def tailConstant : ℝ := 16 * ∑' n : ℕ, Real.exp (-(n:ℝ))

private theorem weight_bound_triple {s r : ℝ} (hs : s ≤ 3) (hr : 0 < r) :
    ‖positiveWeight s r‖ ≤ tailConstant * Real.exp (-r) := by
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2*r by positivity)
  have bound (n : ℕ) :
      ‖Real.exp (s*r^2) * weightedTerm phiPoly n r‖ ≤
        (16 * Real.exp (-r)) * Real.exp (-(n:ℝ)) := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
    have hsq : 1 ≤ ((n:ℝ)+1)^2 := by nlinarith [sq_nonneg (n:ℝ)]
    have hex := Real.one_le_exp (show 0 ≤ 2*r by positivity)
    have hX : 3 * (Real.exp (2*r) + n) ≤ thetaX n r := by
      unfold thetaX
      have hsq' : (n:ℝ) + 1 ≤ ((n:ℝ)+1)^2 := by nlinarith [sq_nonneg (n:ℝ)]
      have hmul := mul_le_mul_of_nonneg_right hsq' (Real.exp_pos (2*r)).le
      have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
        (mul_nonneg (sq_nonneg ((n:ℝ)+1)) (Real.exp_pos (2*r)).le)
      nlinarith [mul_le_mul_of_nonneg_left hex hn]
    have bud : s*r^2 + 3*r/2 + n ≤ thetaX n r/2 := by
      nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg r)]
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
      _ ≤ 16 * Real.exp (-r + -(n:ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ = _ := by rw [Real.exp_add]; ring
  change ‖Real.exp (s*r^2) * ∑' n, weightedTerm phiPoly n r‖ ≤ _
  rw [← tsum_mul_left]
  exact (tsum_of_norm_bounded (Real.summable_exp_neg_nat.mul_left _).hasSum bound).trans_eq
    (by rw [tsum_mul_left]; dsimp [tailConstant]; ring)

private theorem weight_bound {s r : ℝ} (hs : s ≤ 1) (hr : 0 < r) :
    ‖positiveWeight s r‖ ≤ tailConstant * Real.exp (-r) :=
  weight_bound_triple (by linarith) hr

private theorem weight_int {s : ℝ} (hs : s ≤ 1) : IntegrableOn (positiveWeight s) (Ioi 0) := by
  apply ((integrableOn_exp_neg_Ioi 0).const_mul tailConstant).mono'
  · have hc : Continuous phi := continuous_iff_continuousAt.mpr fun x =>
      (thetaSeries_derivative phiPoly x).continuousAt
    exact ((by fun_prop : Continuous (fun r : ℝ => Real.exp (s*r^2))).mul hc).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with r hr
  exact weight_bound hs hr

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

private def gridTest (P : Polynomial ℕ) (N : ℕ) (r : ℝ) :=
  (∑ k ∈ P.support, (P.coeff k : ℝ) * Real.cos ((7*Real.sqrt k)*r)) / N

def test := gridTest witnessPolynomial normalization

private theorem test_continuous (P : Polynomial ℕ) (N : ℕ) : Continuous (gridTest P N) := by
  unfold gridTest
  fun_prop

private theorem gridTest_bound (P : Polynomial ℕ) (N : ℕ) (r : ℝ) :
    |gridTest P N r| ≤ (∑ k ∈ P.support, (P.coeff k : ℝ)) / N := by
  rw [gridTest, abs_div, (abs_of_nonneg (Nat.cast_nonneg N) : |(N : ℝ)| = (N : ℝ))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, (abs_of_nonneg (Nat.cast_nonneg (P.coeff k)) : |(P.coeff k : ℝ)| = (P.coeff k : ℝ))]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (Real.abs_cos_le_one _)

private theorem test_bound (r : ℝ) : |test r| ≤
    (∑ k ∈ witnessPolynomial.support, (witnessPolynomial.coeff k : ℝ)) / normalization :=
  gridTest_bound _ _ _

private theorem grid_mass : (∑ k ∈ witnessPolynomial.support,
    (witnessPolynomial.coeff k : ℝ)) / normalization ≤ 10^10 := by
  have hn : (∑ k ∈ witnessPolynomial.support, witnessPolynomial.coeff k) =
      witnessPolynomial.eval 1 := by simp [Polynomial.eval_eq_sum, Polynomial.sum]
  have he : witnessPolynomial.eval 1 = (∑ p : Fin 10 × Fin 10, pairWeight p)^10 := by
    simp [witnessPolynomial, histogram, Polynomial.eval_finsetSum]
  rw [div_le_iff₀ (show 0 < (normalization:ℝ) by exact_mod_cast normalization_pos)]
  exact_mod_cast (show ∑ k ∈ witnessPolynomial.support, witnessPolynomial.coeff k ≤
    (10:ℕ)^10 * normalization by rw [hn, he]; decide)

private theorem tailConstant_le : tailConstant ≤ 32 := by
  have he : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div, one_div_le_one_div (Real.exp_pos 1) (by norm_num)]
    linarith [Real.add_one_le_exp 1]
  have hs := Real.summable_exp_neg_nat.tsum_le_tsum (g := fun n : ℕ => (1/2:ℝ)^n)
    (fun n => by simpa [← Real.exp_nat_mul] using pow_le_pow_left₀ (Real.exp_pos (-1)).le he n)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hs
  unfold tailConstant
  linarith

theorem d10_remainder : HeatMomentCertificate.errorMass (volume.restrict (Ioi (0:ℝ)))
    (fun r => phi r * test r) ≤ 1/1000000 := by
  let C : ℝ := (1/3^49) * (10^10 * 32)
  have hmajor : ∀ᵐ r ∂(volume.restrict (Ioi (0:ℝ))),
      |phi r * test r| * HeatMomentCertificate.rest (r^2) ≤ C * Real.exp (-r) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with r hr
    have ht := (test_bound r).trans grid_mass
    have hw := weight_bound_triple (s := 3) le_rfl hr
    unfold positiveWeight at hw
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (phi_pos (le_of_lt hr)).le)] at hw
    have hpos := (phi_pos (le_of_lt hr)).le
    rw [abs_mul, abs_of_nonneg hpos]
    calc
      _ ≤ phi r * |test r| * ((1/3^49) * Real.exp (3*r^2)) :=
        mul_le_mul_of_nonneg_left (HeatMomentCertificate.rest_le_triple (sq_nonneg _))
          (mul_nonneg hpos (abs_nonneg _))
      _ = (1/3^49) * (|test r| * positiveWeight 3 r) := by unfold positiveWeight; ring
      _ ≤ (1/3^49) * (10^10 * (tailConstant * Real.exp (-r))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul ht hw (mul_nonneg (Real.exp_pos _).le hpos) (by norm_num)
      _ ≤ C * Real.exp (-r) := by
        dsimp [C]
        calc
          _ ≤ (1/3^49) * (10^10 * (32 * Real.exp (-r))) := by gcongr; exact tailConstant_le
          _ = _ := by ring
  have hi := integral_mono_of_nonneg (ae_of_all _ (fun r => mul_nonneg (abs_nonneg _)
    (sub_nonneg.mpr (Real.sum_le_exp_of_nonneg (sq_nonneg r) 49))))
      ((integrableOn_exp_neg_Ioi 0).const_mul C) hmajor
  rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one] at hi
  exact hi.trans (by norm_num [C])

/-- All three numerical inputs here are independent of the heat parameter. -/
abbrev D10Moments := HeatMomentCertificate.Bounds (volume.restrict (Ioi (0:ℝ)))
  (fun r => phi r * test r)

theorem d10_integral_of_moments (cert : D10Moments) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    (∫ r in Ioi (0:ℝ), positiveWeight s r * test r) ≤ -(1499/1000000 : ℝ) - s/4 := by
  have hphi : Continuous phi := continuous_iff_continuousAt.mpr fun x =>
    (thetaSeries_derivative phiPoly x).continuousAt
  have ht : Continuous test := test_continuous _ _
  have hi := (weight_int (s := 1) le_rfl).mul_bdd (g := fun r => |test r|) (c := 10^10)
    ht.abs.aestronglyMeasurable (ae_of_all _ (fun r => by rw [Real.norm_eq_abs, abs_abs]; exact (test_bound r).trans grid_mass))
  have hdom : IntegrableOn (fun r => |phi r * test r| * Real.exp (r^2)) (Ioi 0) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with r hr
    rw [abs_mul, abs_of_nonneg (phi_pos (le_of_lt hr)).le]
    simp only [positiveWeight, one_mul]
    ring
  have hu := HeatMomentCertificate.uniform_of_moments _ _ (hphi.mul ht).aestronglyMeasurable hdom cert d10_remainder hs.1 hs.2
  convert hu using 1
  apply integral_congr_ae
  filter_upwards with r
  simp only [positiveWeight, Pi.mul_apply]
  ring

/-- The parameter-uniform scalar inequality checked in certify_d10_heat.py
is enough to refute PSD, using the actual finite grid and coefficients. -/
theorem d10_failure {s : ℝ} (hs : s ≤ 1)
    (cert : (∫ r in Ioi (0:ℝ), positiveWeight s r * test r) < 0) : s ∉ A 10 := by
  let b (k : ℕ) (r : ℝ) := positiveWeight s r * Real.cos ((7*Real.sqrt k)*r)
  have hi (k) : IntegrableOn (b k) (Ioi 0) := (weight_int hs).mul_bdd (c := 1)
    (by fun_prop) (ae_of_all _ fun _ => Real.abs_cos_le_one _)
  have he (r : ℝ) : positiveWeight s r * test r =
      (∑ k ∈ witnessPolynomial.support, (witnessPolynomial.coeff k : ℝ) * b k r) / normalization := by
    simp only [test, gridTest, mul_div_assoc', Finset.mul_sum, b]
    apply congrArg (fun a : ℝ => a / (normalization : ℝ))
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he] at cert
  rw [integral_div, integral_finsetSum _ (fun k _ => (hi k).const_mul _)] at cert
  simp_rw [integral_const_mul] at cert
  have hn := (div_lt_iff₀ (show (0:ℝ) < normalization by exact_mod_cast normalization_pos)).mp cert
  rw [zero_mul] at hn
  apply not_radialPSD_of_negative
  change (∑ k ∈ witnessPolynomial.support, (witnessPolynomial.coeff k : ℝ) *
    ((2 * ∫ r in Ioi (0:ℝ), b k r) / numerator s 0)) < 0
  simp only [mul_div_assoc', ← Finset.sum_div]
  apply div_neg_of_neg_of_pos _ (mass_pos hs)
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

private theorem phi_smooth : ContDiff ℝ ∞ phi := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro k _
  rw [p_iter]
  exact fun x => (dp k x).differentiableAt

private theorem jet_smooth (j : ℕ) : ContDiffOn ℝ ∞ (jet j) (Ioi 0) := by
  induction j with
  | zero =>
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ ∞ (fun r => Real.exp (r/16) * phi (Real.sqrt r)) x
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun r : ℝ => Real.exp (r/16)) x).mul
      (phi_smooth.contDiffAt.comp x (Real.contDiffAt_sqrt (ne_of_gt hx)))
  | succ j ih => exact (ih.deriv_of_isOpen isOpen_Ioi (by simp)).neg.div_const _

theorem jet_iter (j : ℕ) : jet j = fun x =>
    (-Real.pi⁻¹)^j * iteratedDeriv j (jet 0) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    funext x
    change -(deriv (jet j) x) / Real.pi = _
    rw [ih, deriv_const_mul_field, iteratedDeriv_succ, pow_succ]
    ring

abbrev FourthPositive := ∀ x > 0, 0 < iteratedDeriv 4 (jet 0) x

/-- The exact polynomial-in-derivatives expression enclosed by Arb. -/
def Q4 (x : ℝ) := ∑ i ∈ Finset.range 5, ((4 : ℕ).choose i : ℝ) *
    (1/16 : ℝ)^(4-i) * iteratedDeriv i (profile 0) x

theorem fourth_of_Q4 (cert : ∀ x > 0, 0 < Q4 x) : FourthPositive := by
  intro x hx
  have hh : ContDiffAt ℝ 4 (profile 0) x :=
    (phi_smooth.of_le (show (4 : ℕ∞ω) ≤ ∞ by simp)).contDiffAt.comp x
      (Real.contDiffAt_sqrt hx.ne')
  have eq : jet 0 = fun r => profile 0 r * Real.exp ((1/16)*r) := by
    funext r
    simp only [jet, one_div_mul_eq_div, mul_comm (profile 0 r)]
  rw [eq, PaperIIAudit.heatDerivative hh]
  exact mul_pos (Real.exp_pos _) (cert x hx)

private theorem fourth_pos (h : FourthPositive) {x : ℝ} (hx : 0 < x) : 0 < jet 4 x := by
  rw [jet_iter]
  rw [show (-Real.pi⁻¹)^4 = (Real.pi⁻¹)^4 by ring]
  exact mul_pos (pow_pos (inv_pos.mpr Real.pi_pos) _) (h x hx)

private theorem jet_deriv (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (jet j) (-Real.pi * jet (j+1) x) x := by
  have hd := ((jet_smooth j).differentiableOn (by simp) x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
  convert hd.hasDerivAt using 1
  simp only [jet]
  field_simp [Real.pi_ne_zero]

private theorem base_decay : Tendsto (jet 0) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun x : ℝ => tailConstant * Real.exp (-Real.sqrt x))
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simpa only [jet, profile,raw,p,Q, positiveWeight, Real.sq_sqrt hx.le, one_div_mul_eq_div] using
      (weight_bound (s := 1/16) (by norm_num) (Real.sqrt_pos.mpr hx))
  · simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop).const_mul tailConstant

/-- Every derivative has arbitrarily small values arbitrarily far out.
Two distant small values of the previous derivative suffice by the MVT. -/
private theorem jet_small (j : ℕ) (R ε : ℝ) (hε : 0 < ε) :
    ∃ x > R, |jet j x| < ε := by
  induction j generalizing R ε with
  | zero =>
    have h := (Metric.tendsto_nhds.mp base_decay ε hε).and (eventually_gt_atTop R)
    obtain ⟨x,hx,hR⟩ := h.exists
    exact ⟨x, hR, by simpa [Real.dist_eq] using hx⟩
  | succ j ih =>
    obtain ⟨a,ha,ha'⟩ := ih (max R 0) (ε/4) (by positivity)
    obtain ⟨b,hb,hb'⟩ := ih (a+1) (ε/4) (by positivity)
    have ha0 : 0 < a := (le_max_right _ _).trans_lt ha
    have hab : a < b := by linarith
    have inc : Icc a b ⊆ Ioi (0:ℝ) := fun x hx => ha0.trans_le hx.1
    obtain ⟨x,hx,eq⟩ := exists_hasDerivAt_eq_slope (jet j) (fun x => -Real.pi * jet (j+1) x)
      hab ((jet_smooth j).continuousOn.mono inc) (fun x hx => jet_deriv j (ha0.trans hx.1))
    refine ⟨x, ((le_max_left _ _).trans_lt ha).trans hx.1, ?_⟩
    have hgap : 1 ≤ b-a := by linarith
    have hh := congrArg abs eq
    rw [abs_mul, abs_neg, abs_of_pos Real.pi_pos, abs_div, abs_of_pos (sub_pos.mpr hab)] at hh
    have hs : |jet j b - jet j a| < ε := (abs_sub _ _).trans_lt (by linarith)
    have hq := div_le_self (abs_nonneg (jet j b - jet j a)) hgap
    nlinarith [Real.pi_gt_three, mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (abs_nonneg (jet (j+1) x))]

private theorem witnessStep {j : ℕ} (pos : ∀ x > 0, 0 < jet (j+1) x) :
    GenesisD9Fourier.OpenStep (jet j) (jet (j+1)) := by
  refine ⟨fun x hx => jet_deriv j hx, ?_⟩
  have anti : StrictAntiOn (jet j) (Ioi 0) := strictAntiOn_of_deriv_neg (convex_Ioi _)
    (jet_smooth j).continuousOn (by
      rw [isOpen_Ioi.interior_eq]
      intro x hx
      rw [(jet_deriv j hx).deriv]
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (pos x hx))
  have hn {x : ℝ} (hx : 0 < x) : 0 ≤ jet j x := by
    by_contra! h
    obtain ⟨y,hy,hy'⟩ := jet_small j x _ (neg_pos.mpr h)
    have hlt := anti hx (hx.trans hy) hy
    linarith [(abs_lt.mp hy').1]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a,ha,ha'⟩ := jet_small j 0 ε hε
  filter_upwards [eventually_gt_atTop a] with x hx
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hn (ha.trans hx))]
  exact (anti ha (ha.trans hx) hx).trans ((le_abs_self _).trans_lt ha')

private theorem jet_meas (j : ℕ) : Measurable (jet j) := by
  cases j with
  | zero => exact (by fun_prop : Measurable (fun x : ℝ => Real.exp (x/16))).mul (profile_meas 0 (by decide))
  | succ j => exact (measurable_deriv (jet j)).neg.div_const _

theorem rational_D9 (h : FourthPositive) : (1/16 : ℝ) ∈ A 9 := by
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
  have s3 := witnessStep (j := 3) (fun _ hx => fourth_pos h hx)
  have p3 := s3.pos (fun _ hx => fourth_pos h hx)
  have s2 := witnessStep p3
  have p2 := s2.pos p3
  have s1 := witnessStep p2
  have p1 := s1.pos p2
  have s0 := witnessStep p1
  have t1 := GenesisD9Fourier.lift_positive hi (jet_meas 1) p1 s0 base
  have t2 := GenesisD9Fourier.lift_positive t1.1 (jet_meas 2) p2 s1 t1.2
  have t3 := GenesisD9Fourier.lift_positive t2.1 (jet_meas 3) p3 s2 t2.2
  have t4 := GenesisD9Fourier.lift_positive t3.1 (jet_meas 4) (fun _ hx => fourth_pos h hx) s3 t3.2
  let f := fun k : E 9 => if k = 0 then 0 else jet 4 (‖k‖^2) / numerator (1/16) 0
  have heq : f =ᵐ[volume] fun k => jet 4 (‖k‖^2) / numerator (1/16) 0 := by
    filter_upwards [volume.ae_ne (0 : E 9)] with k hk
    simp [f, hk]
  apply GenesisTidal.radialPSD_of_cosine_density f ((t4.1.div_const _).congr heq.symm)
  · intro k
    by_cases hk : k = 0
    · simp [f, hk]
    · simpa [f, hk] using (div_pos (fourth_pos h (sq_pos_of_pos (norm_pos_iff.mpr hk))) hzpos).le
  · intro x
    rw [F, ← t4.2 x, GenesisD9Fourier.transform, ← integral_div]
    apply integral_congr_ae
    filter_upwards [heq] with k hk
    rw [hk]
    ring

/-- An explicit positive D9 witness suffices. The paper's D9 endpoint
exceeds 1/16, and the published threshold bound is below 1/16. -/
theorem concreteCutoff {L : ℝ} (hL : 0 ≤ L) (hupper : L ≤ 0.22)
    (deBruijnNewman : ∀ t, (∀ z : ℂ, newmanH t z = 0 → z.im = 0) ↔ L ≤ t)
    (witnessBounds : ∀ x > 0, 0 < Q4 x)
    (upper9 : A 9 ⊆ Iic 1)
    (cert : D10Moments)
    {d : ℕ} (_hd : 1 ≤ d) : (A d ∩ B).Nonempty ↔ d ≤ 9 := by
  have realZeros := zeroThreshold L deBruijnNewman
  have restrictDim {a b : ℕ} (hab : a ≤ b) {s : ℝ} (h : s ∈ A b) : s ∈ A a :=
    GenesisFormalV5.euclideanPSD_lower (F s) hab h
  constructor
  · rintro ⟨s, ha, hb⟩
    by_contra h
    rw [realZeros] at hb
    have hs : 0 ≤ s := le_trans (by positivity : 0 ≤ L/4) hb
    have ten := restrictDim (a := 10) (by omega) ha
    have capped : s ≤ 1 := upper9 (restrictDim (by decide : 9 ≤ 10) ten)
    exact d10_failure capped ((d10_integral_of_moments cert ⟨hs,capped⟩).trans_lt (by linarith)) ten
  · intro h
    refine ⟨1/16, restrictDim h (rational_D9 (fourth_of_Q4 witnessBounds)), ?_⟩
    rw [realZeros]
    change L/4 ≤ 1/16
    linarith

#print axioms entire_on_real
#print axioms heatScaling
#print axioms zeroThreshold
#print axioms zero_profile
#print axioms d10_remainder
#print axioms d10_integral_of_moments
#print axioms d10_failure
#print axioms fourth_of_Q4
#print axioms rational_D9
#print axioms concreteCutoff
end XiCoexistence
