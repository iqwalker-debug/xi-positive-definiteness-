import XiCutoff
import D9DirectSigns
import D10Rows

noncomputable section
open MeasureTheory Complex
open scoped Topology InnerProductSpace BigOperators
namespace GenesisTidalMellin
abbrev E := GenesisD9Fourier.E

def StrictRadial (d : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → E d), Function.Injective x →
    ∀ c : Fin n → ℝ, c ≠ 0 →
      0 < ∑ i, ∑ j, c i * c j * F (dist (x i) (x j))

private def planeWave {d : ℕ} (x : E d) : Multiplicative (E d) →* ℂ where
  toFun k := Complex.exp ((⟪k.toAdd, x⟫_ℝ : ℂ) * I)
  map_one' := by simp
  map_mul' k l := by simp [inner_add_left, add_mul, Complex.exp_add]

private theorem planeWave_injective {d : ℕ} : Function.Injective (@planeWave d) := by
  intro x y he
  by_contra hxy
  let z := x-y
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy
  have hn := (real_inner_self_pos.mpr hz).ne'
  let k : E d := (Real.pi / ⟪z,z⟫_ℝ) • z
  have hp : ⟪k,x⟫_ℝ - ⟪k,y⟫_ℝ = Real.pi := by
    rw [← inner_sub_right]
    change ⟪k,z⟫_ℝ = _
    rw [show k = (Real.pi / ⟪z,z⟫_ℝ) • z from rfl, real_inner_smul_left]
    exact div_mul_cancel₀ _ hn
  have h := congrArg (fun f : Multiplicative (E d) →* ℂ => f (Multiplicative.ofAdd k)) he
  change Complex.exp ((⟪k,x⟫_ℝ : ℂ)*I) = Complex.exp ((⟪k,y⟫_ℝ : ℂ)*I) at h
  have h' := congrArg (fun v => v / Complex.exp ((⟪k,y⟫_ℝ : ℂ)*I)) h
  rw [← Complex.exp_sub, div_self (Complex.exp_ne_zero _), ← sub_mul, ← ofReal_sub, hp,
    Complex.exp_pi_mul_I] at h'
  norm_num at h'

theorem strict_of_density {d : ℕ} {F : ℝ → ℝ} {f : E d → ℝ}
    (hf : Integrable f) (hp : ∀ᵐ k ∂volume, 0 < f k)
    (hinv : ∀ x : E d, F ‖x‖ = ∫ k, f k * Real.cos ⟪k,x⟫_ℝ) :
    StrictRadial d F := by
  intro n x hx c hc
  let a (i : Fin n) (k : E d) := ⟪k,x i⟫_ℝ
  let C (k : E d) := ∑ i, c i * Real.cos (a i k)
  let S (k : E d) := ∑ i, c i * Real.sin (a i k)
  let P (k : E d) := C k ^ 2 + S k ^ 2
  let g (i j : Fin n) (k : E d) := c i * c j * (f k * Real.cos (a i k - a j k))
  have hg (i j : Fin n) : Integrable (g i j) :=
    (hf.mul_bdd (c := 1) (by dsimp [a]; fun_prop)
      (Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _)).const_mul _
  have hrow (i : Fin n) : Integrable (fun k => ∑ j, g i j k) :=
    integrable_finsetSum Finset.univ fun j _ => hg i j
  have hsum : Integrable (fun k => ∑ i, ∑ j, g i j k) :=
    integrable_finsetSum Finset.univ fun i _ => hrow i
  have hexpr (k : E d) : (∑ i, ∑ j, g i j k) = f k * P k := by
    unfold P C S
    calc
      _ = f k * (∑ i, ∑ j, c i * c j * Real.cos (a i k - a j k)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by dsimp [g]; ring
      _ = _ := by
        simp only [Real.cos_sub, mul_add, Finset.sum_add_distrib, GenesisFormalV5.rankOne_quadratic]
  have hGram : (∑ i, ∑ j, c i * c j * F (dist (x i) (x j))) = ∫ k, f k * P k := by
    simp_rw [← hexpr]
    rw [integral_finsetSum Finset.univ (fun i _ => hrow i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => hg i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [dist_eq_norm, hinv, ← integral_const_mul]
    simp [g, a, inner_sub_right]
  have hnn (k : E d) : 0 ≤ P k := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [hGram]
  have hfi : Integrable (fun k => f k * P k) := hsum.congr (Filter.Eventually.of_forall hexpr)
  have hn : ∀ᵐ k ∂volume, 0 ≤ f k * P k :=
    hp.mono fun k hk => mul_nonneg hk.le (hnn k)
  by_contra h
  have hz : (∫ k, f k * P k) = 0 :=
    le_antisymm (le_of_not_gt h) (integral_nonneg_of_ae hn)
  have ha : (fun k => f k * P k) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hn hfi).mp hz
  have hb : P =ᵐ[volume] 0 := by
    filter_upwards [hp, ha] with k hk hzero
    exact (mul_eq_zero.mp hzero).resolve_left hk.ne'
  have hP : P = 0 := Measure.eq_of_ae_eq hb (by dsimp [P,C,S,a]; fun_prop) continuous_const
  have hCS (k : E d) : C k = 0 ∧ S k = 0 := by
    have hzero : C k ^ 2 + S k ^ 2 = 0 := congrFun hP k
    constructor <;> nlinarith [sq_nonneg (C k), sq_nonneg (S k)]
  have hLI := (linearIndependent_monoidHom (Multiplicative (E d)) ℂ).comp
    (planeWave ∘ x) (planeWave_injective.comp hx)
  have hzero : ∑ i : Fin n, (c i : ℂ) • ((planeWave (x i) : Multiplicative (E d) →* ℂ) :
      Multiplicative (E d) → ℂ) = 0 := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    change (∑ i, (c i : ℂ) * Complex.exp ((a i k.toAdd : ℂ) * I)) = 0
    simp only [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_add,
      ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum]
    change (C k.toAdd : ℂ) + (S k.toAdd : ℂ) * I = 0
    simp [(hCS k.toAdd).1, (hCS k.toAdd).2]
  have hall := (Fintype.linearIndependent_iff.mp hLI) (fun i => (c i : ℂ)) hzero
  apply hc
  funext i
  exact_mod_cast hall i

theorem StrictRadial.lower {d e : ℕ} {F : ℝ → ℝ} (hle : d ≤ e)
    (hs : StrictRadial e F) : StrictRadial d F := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => exact hs
  | succ k ih =>
    apply ih
    intro n x hx c hc
    have hpad := GenesisFormalV5.euclideanPad_dist (d+k)
    have he : Function.Injective (GenesisFormalV5.euclideanPad (d+k)) := by
      intro x y he
      have hd := hpad x y
      rw [he, dist_self] at hd
      exact dist_eq_zero.mp hd.symm
    simpa only [Function.comp_apply, hpad] using
      hs n (GenesisFormalV5.euclideanPad (d+k) ∘ x) (he.comp hx) c hc

/-- Positivity of the dimension-nine numerator from the direct theta-series
sign proofs. No Arb table is used. -/
theorem numerator_positive_direct (r : ℝ) (hr : 0 < r) : 0 < N r := by
  by_cases h : r ≤ 1/5
  · exact GenesisD9Fourier.near_numerator_pos p (b := 1/5)
      (fun j _ => continuous_iff_continuousAt.mpr fun t => (dp j t).continuousAt)
      (fun j _ => dp j) (odd_jet 1 (by decide)) (odd_jet 3 (by decide))
      (odd_jet 5 (by decide)) (odd_jet 7 (by decide))
      (fun t ht => DirectSigns.near_eighth ht.1.le ht.2.le) r ⟨hr,h⟩
  · exact DirectSigns.positive_middle (le_of_not_ge h)

theorem strict_d9 : StrictRadial 9 GenesisTidal.criticalXiProfile := by
  obtain ⟨f, hf, _, hp, hinv⟩ := d9_density_of_positive_numerator numerator_positive_direct
  have ha : ∀ᵐ k ∂volume, 0 < f k := (volume.ae_ne (0 : E 9)).mono hp
  exact strict_of_density hf ha hinv

open GenesisD10Table GenesisD10Witness in
/-- Strict positivity on distinct points through dimension nine and a finite
obstruction thereafter. Only the D10 transcendental enclosures are external. -/
theorem strict_cutoff_of_arb
    (hret : List.Forall₂ (fun (x : ℝ) (u : ℤ) => x ≤ (u : ℝ) / 1000000000000000000)
      (contributions GenesisTidal.criticalXiProfile
        (witnessPolynomial.support.filter (fun k => k ≤ 293))) retainedUnits)
    (hom : List.Forall₂ (fun (x : ℝ) (u : ℤ) => x ≤ (u : ℝ) / 1000000000000000000)
      (contributions GenesisTidal.criticalXiProfile
        (witnessPolynomial.support.filter (fun k => ¬ k ≤ 293))) omittedUnits)
    (d : ℕ) :
    (d ≤ 9 → StrictRadial d GenesisTidal.criticalXiProfile) ∧
    (10 ≤ d → ¬ GenesisFormalV4.RadialPSD (E d) GenesisTidal.criticalXiProfile) :=
  ⟨strict_d9.lower, fun hd =>
    GenesisFormalV5.euclideanPSD_higher_failure _ hd (xi_not_radialPSD_d10_of_row_bounds hret hom)⟩

open GenesisD10Table GenesisD10Witness in
/-- The exact cutoff with only the D10 row enclosures as external inputs.
Dimension nine comes from `numerator_positive_direct`, so the two D9 Arb
tables required by `exact_cutoff_of_arb` are not hypotheses here. -/
theorem exact_cutoff_of_row_bounds
    (hret : List.Forall₂ (fun (x : ℝ) (u : ℤ) => x ≤ (u : ℝ) / 1000000000000000000)
      (contributions GenesisTidal.criticalXiProfile
        (witnessPolynomial.support.filter (fun k => k ≤ 293))) retainedUnits)
    (hom : List.Forall₂ (fun (x : ℝ) (u : ℤ) => x ≤ (u : ℝ) / 1000000000000000000)
      (contributions GenesisTidal.criticalXiProfile
        (witnessPolynomial.support.filter (fun k => ¬ k ≤ 293))) omittedUnits)
    (d : ℕ) :
    GenesisFormalV4.RadialPSD (E d) GenesisTidal.criticalXiProfile ↔ d ≤ 9 := by
  obtain ⟨f, hf, hn, _, hinv⟩ := d9_density_of_positive_numerator numerator_positive_direct
  exact GenesisTidal.criticalXi_cutoff_of_boundary_dimensions
    (GenesisTidal.radialPSD_of_cosine_density f hf hn hinv)
    (xi_not_radialPSD_d10_of_row_bounds hret hom) d

end GenesisTidalMellin
#print axioms GenesisTidalMellin.strict_d9
#print axioms GenesisTidalMellin.strict_cutoff_of_arb
#print axioms GenesisTidalMellin.exact_cutoff_of_row_bounds
