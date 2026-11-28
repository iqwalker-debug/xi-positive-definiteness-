import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory
open scoped BigOperators

namespace GaussianTilt

private theorem expSeries (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / k.factorial) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- On a shell of radius R, positivity against every raised shell power
implies positivity against the Gaussian tilt. The signed test q may
include the base shell density. No sign assumption on q is needed. -/
theorem shellTilt_nonneg (μ : Measure ℝ) (q : ℝ → ℝ) (R c : ℝ)
    (hc : 0 ≤ c) (hq : Integrable q μ)
    (hR : ∀ᵐ u ∂μ, u ^ 2 ≤ R ^ 2)
    (hMom : ∀ k : ℕ, 0 ≤ ∫ u, (R ^ 2 - u ^ 2) ^ k * q u ∂μ) :
    0 ≤ ∫ u, Real.exp (-c * u ^ 2) * q u ∂μ := by
  let term (k : ℕ) (u : ℝ) := (c * (R ^ 2 - u ^ 2)) ^ k / k.factorial * q u
  let bound (k : ℕ) (u : ℝ) := (c * R ^ 2) ^ k / k.factorial * ‖q u‖
  have hb (u : ℝ) : HasSum (fun k => bound k u) (Real.exp (c * R^2) * ‖q u‖) :=
    (expSeries _).mul_right _
  have hseries : HasSum (fun k => ∫ u, term k u ∂μ)
      (∫ u, Real.exp (c * (R^2 - u^2)) * q u ∂μ) := by
    apply hasSum_integral_of_dominated_convergence bound
    · intro k
      exact (by fun_prop : Continuous (fun u : ℝ =>
        (c * (R ^ 2 - u ^ 2)) ^ k / (k.factorial : ℝ))).aestronglyMeasurable.mul hq.1
    · intro k
      filter_upwards [hR] with u hu
      have h₀ := mul_nonneg hc (sub_nonneg.mpr hu)
      have h₁ : c * (R^2-u^2) ≤ c * R^2 :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg u)) hc
      dsimp [term, bound]
      rw [abs_mul, abs_of_nonneg (div_nonneg (pow_nonneg h₀ _) (by positivity))]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ h₀ h₁ _) (by positivity)) (abs_nonneg _)
    · exact ae_of_all _ fun u => (hb u).summable
    · simpa only [(hb _).tsum_eq] using hq.norm.const_mul (Real.exp (c * R^2))
    · exact ae_of_all _ fun u => (expSeries _).mul_right _
  have hterm (k : ℕ) : 0 ≤ ∫ u, term k u ∂μ := by
    have heq (u : ℝ) : term k u = (c^k / k.factorial) * ((R^2-u^2)^k * q u) := by
      simp only [term, mul_pow, div_eq_mul_inv]
      ring
    simp_rw [heq, integral_const_mul]
    exact mul_nonneg (div_nonneg (pow_nonneg hc _) (by positivity)) (hMom k)
  have hpos : 0 ≤ ∑' k, ∫ u, term k u ∂μ := tsum_nonneg hterm
  rw [hseries.tsum_eq] at hpos
  have hfactor (u : ℝ) : Real.exp (-c * u^2) * q u =
      Real.exp (-c * R^2) * (Real.exp (c * (R^2-u^2)) * q u) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hfactor, integral_const_mul]
  exact mul_nonneg (Real.exp_pos _).le hpos

/-- Real Gram test for a kernel on a finite configuration. -/
def gram {n : ℕ} (w : Fin n → ℝ) (K : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * K i j

private theorem integralGram {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Fin n → ℝ)
    (f : Fin n → Fin n → Ω → ℝ) (hf : ∀ i j, Integrable (f i j) μ) :
    (∫ u, gram w (fun i j => f i j u) ∂μ) = gram w (fun i j => ∫ u, f i j u ∂μ) := by
  have hi (i j) := (hf i j).const_mul (w i * w j)
  unfold gram
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul]

/-- A projected sphere supplies phases at the configuration points. The
cosine of their differences has a nonnegative Gram form for every positive
spectral measure. The marginal-density identity enters as an explicit input. -/
theorem projectedMoment_nonneg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure Ω) (w : Fin n → ℝ) (phase : Fin n → Ω → ℝ)
    (entry : Fin n → Fin n → ℝ) (scale : ℝ) (hs : 0 ≤ scale)
    (hi : ∀ i j, Integrable (fun z => Real.cos (phase i z - phase j z)) σ)
    (marginal : ∀ i j, entry i j =
      scale * ∫ z, Real.cos (phase i z - phase j z) ∂σ) :
    0 ≤ gram w entry := by
  have hpoint (z : Ω) :
      gram w (fun i j => Real.cos (phase i z - phase j z)) =
      (∑ i, w i * Real.cos (phase i z))^2 + (∑ i, w i * Real.sin (phase i z))^2 := by
    simp only [gram, Real.cos_sub, pow_two, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hn : 0 ≤ ∫ z, gram w (fun i j => Real.cos (phase i z - phase j z)) ∂σ :=
    integral_nonneg fun z => (hpoint z).symm ▸ add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [integralGram _ _ _ hi] at hn
  have heq : gram w entry =
      scale * gram w (fun i j => ∫ z, Real.cos (phase i z - phase j z) ∂σ) := by
    simp only [gram, marginal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  exact mul_nonneg hs hn

/-- Apply the shell lemma to an actual Gram test. The geometric input
is positivity of the unweighted raised-shell kernels on the configuration.
Their positive normalization constants may be absorbed into the kernels. -/
theorem shellGram_nonneg {n : ℕ} (μ : Measure ℝ) (R c : ℝ) (hc : 0 ≤ c)
    (hR : ∀ᵐ u ∂μ, u^2 ≤ R^2) (w : Fin n → ℝ) (K : Fin n → Fin n → ℝ → ℝ)
    (hInt : ∀ (k : ℕ) i j, Integrable (fun u => (R^2-u^2)^k * K i j u) μ)
    (hGram : ∀ k : ℕ, 0 ≤ gram w (fun i j => ∫ u, (R^2-u^2)^k * K i j u ∂μ)) :
    0 ≤ ∫ u, Real.exp (-c*u^2) * gram w (fun i j => K i j u) ∂μ := by
  apply shellTilt_nonneg μ _ R c hc _ hR
  · intro k
    have heq (u : ℝ) : (R^2-u^2)^k * gram w (fun i j => K i j u) =
        gram w (fun i j => (R^2-u^2)^k * K i j u) := by
      simp only [gram, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [heq]
    rw [integralGram _ _ _ (hInt k)]
    exact hGram k
  · apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    simpa using (hInt 0 i j).const_mul (w i * w j)

/-- Mix shell Gram forms, then divide by the positive mass of the tilt. -/
theorem mixtureGram_nonneg {n : ℕ} (ν : Measure ℝ) (μ : ℝ → Measure ℝ)
    (c mass : ℝ) (hc : 0 ≤ c) (hmass : 0 < mass) (w : Fin n → ℝ)
    (K : Fin n → Fin n → ℝ → ℝ)
    (support : ∀ᵐ R ∂ν, ∀ᵐ u ∂(μ R), u^2 ≤ R^2)
    (moments : ∀ᵐ R ∂ν, ∀ (k : ℕ) i j,
      Integrable (fun u => (R^2-u^2)^k * K i j u) (μ R))
    (projected : ∀ᵐ R ∂ν, ∀ k : ℕ,
      0 ≤ gram w (fun i j => ∫ u, (R^2-u^2)^k * K i j u ∂(μ R))) :
    0 ≤ (∫ R, ∫ u, Real.exp (-c*u^2) * gram w (fun i j => K i j u) ∂(μ R) ∂ν) / mass := by
  apply div_nonneg _ hmass.le
  apply integral_nonneg_of_ae
  filter_upwards [support, moments, projected] with R hR hInt hGram
  exact shellGram_nonneg _ _ _ hc hR w K hInt hGram

/-- Set-theoretic cutoff using exactly the D9 witness, D10 obstruction,
D10 downward closure, dimension restriction, and nonnegative zero threshold. -/
theorem coexistenceCutoff (A : ℕ → Set ℝ) (B : Set ℝ)
    (restrictDim : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → A b ⊆ A a)
    (witness : (A 9 ∩ B).Nonempty) (excluded : 0 ∉ A 10)
    (downTen : ∀ {s t : ℝ}, s ∈ A 10 → t ≤ s → t ∈ A 10)
    (threshold : B ⊆ Set.Ici 0) {d : ℕ} (hd : 1 ≤ d) :
    (A d ∩ B).Nonempty ↔ d ≤ 9 := by
  constructor
  · rintro ⟨s, hs, hB⟩
    by_contra h
    exact excluded (downTen (restrictDim (by decide : 1 ≤ 10) (by omega) hs) (threshold hB))
  · rintro h
    obtain ⟨s, hs, hB⟩ := witness
    exact ⟨s, restrictDim hd h hs, hB⟩

#print axioms shellTilt_nonneg
#print axioms projectedMoment_nonneg
#print axioms shellGram_nonneg
#print axioms mixtureGram_nonneg
#print axioms coexistenceCutoff
end GaussianTilt
