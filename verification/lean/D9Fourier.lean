import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A real cosine-transform dimension walk for densities expressed in squared radius.
Frequencies use the angular convention cos ⟪k,x⟫. -/
noncomputable section
namespace GenesisD9Fourier
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Angular cosine transform in dimension n. -/
def transform {n : ℕ} (G : ℝ → ℝ) (x : E n) : ℝ :=
  ∫ k : E n, G (‖k‖ ^ 2) * Real.cos ⟪k, x⟫_ℝ

theorem transform_eq_of_norm_eq {n : ℕ} (G : ℝ → ℝ) {x y : E n} (h : ‖x‖ = ‖y‖) :
    transform G x = transform G y := by
  let R := (ℝ ∙ (x-y))ᗮ.reflection
  have he : R x = y := Submodule.reflection_sub h
  have hv := R.measurePreserving.integral_comp R.toMeasurableEquiv.measurableEmbedding
    (fun k => G (‖k‖ ^ 2) * Real.cos ⟪k, y⟫_ℝ)
  unfold transform
  rw [← hv]
  simp only [← he, R.inner_map_map, R.norm_map]

/-- Euclidean isometry used to split off the last two coordinates. -/
def split (n : ℕ) : E (n+2) ≃ₗᵢ[ℝ] WithLp 2 (E n × E 2) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ => ℝ))

def embed {n : ℕ} (x : E n) : E (n+2) := (split n).symm (WithLp.toLp 2 (x,0))

theorem norm_embed {n : ℕ} (x : E n) : ‖embed x‖ = ‖x‖ := by
  rw [embed, LinearIsometryEquiv.norm_map]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp

def splitMeas (n : ℕ) : E (n+2) ≃ᵐ E n × E 2 :=
  (split n).toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 _).symm

theorem split_preserves (n : ℕ) : MeasurePreserving (splitMeas n) :=
  (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod (E n) (E 2)).comp
    (split n).measurePreserving

theorem plane_integral (H : ℝ → ℝ) (a : ℝ) :
    (∫ v : E 2, H (a + ‖v‖ ^ 2)) =
      ∫ p : ℝ × ℝ, H (a + (p.1 ^ 2 + p.2 ^ 2)) := by
  let e : E 2 ≃ᵐ ℝ × ℝ := (MeasurableEquiv.toLp 2 _).symm.trans MeasurableEquiv.finTwoArrow
  have hv : MeasurePreserving e := (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
  rw [← hv.integral_comp' (fun p => H (a + (p.1 ^ 2 + p.2 ^ 2)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, e]

/-- Restrict the transform to the embedded subspace by Fubini. -/
theorem transform_embed {n : ℕ} (H G : ℝ → ℝ) (x : E n)
    (hI : Integrable (fun k : E (n+2) => H (‖k‖ ^ 2)))
    (hm : ∀ a ≥ (0 : ℝ), (∫ v : E 2, H (a + ‖v‖ ^ 2)) = G a) :
    transform H (embed x) = transform G x := by
  let f := fun p : E n × E 2 => H (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)
  let g := fun p : E n × E 2 => f p * Real.cos ⟪p.1, x⟫_ℝ
  have hn (k : E (n+2)) : ‖k‖ ^ 2 =
      ‖(splitMeas n k).1‖ ^ 2 + ‖(splitMeas n k).2‖ ^ 2 := by
    rw [← (split n).norm_map k]
    exact WithLp.prod_norm_sq_eq_of_L2 _
  have hp (k : E (n+2)) : ⟪k, embed x⟫_ℝ = ⟪(splitMeas n k).1, x⟫_ℝ := by
    rw [← (split n).inner_map_map k (embed x)]
    simp [embed, WithLp.prod_inner_apply, splitMeas]
  have hf : Integrable f := ((split_preserves n).integrable_comp_emb
    (splitMeas n).measurableEmbedding).mp (by simpa only [Function.comp_def, f, ← hn] using hI)
  have hc : Continuous (fun p : E n × E 2 => Real.cos ⟪p.1, x⟫_ℝ) := by fun_prop
  have hg : Integrable g := hf.norm.mono' (hf.aestronglyMeasurable.mul hc.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => by
      dsimp [g]
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
  calc
    transform H (embed x) = ∫ k, g (splitMeas n k) := by
      unfold transform
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun k => by
        change H (‖k‖ ^ 2) * Real.cos ⟪k, embed x⟫_ℝ = _
        simp only [hn k, hp k, g, f]
    _ = ∫ p, g p := (split_preserves n).integral_comp' _
    _ = ∫ u : E n, ∫ v : E 2, g (u,v) := integral_prod _ hg
    _ = transform G x := by
      unfold transform
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        simp only [g, f, integral_mul_const, hm _ (sq_nonneg _)]

/-- Polar integration for profiles indexed by squared radius, avoiding
a square-root substitution at zero. -/
theorem planar_sq_profile_integral (a : ℝ) (G : ℝ → ℝ) :
    (∫ p : ℝ × ℝ, G (a + (p.1 ^ 2 + p.2 ^ 2))) =
      (2 * Real.pi) * ∫ r in Ioi (0 : ℝ), r * G (a + r ^ 2) := by
  calc
    _ = ∫ p in polarCoord.target, p.1 * G (a + p.1 ^ 2) := by
      rw [← integral_comp_polarCoord_symm]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        simp only [polarCoord_symm_apply, smul_eq_mul]
        have h : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
          calc
            _ = p.1 ^ 2 * (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) := by ring
            _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]
        rw [h]
    _ = (∫ r in Ioi (0 : ℝ), r * G (a + r ^ 2)) *
          ∫ θ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← setIntegral_prod_mul]
      simp only [polarCoord_target, mul_one, Measure.volume_eq_prod]
    _ = _ := by
      rw [mul_comm]
      congr 1
      simp only [setIntegral_const, smul_eq_mul, mul_one]
      rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg])]
      ring

/-- Analytic hypotheses on two consecutive squared-radius profiles.
The derivative is needed only on positive squared radii. -/
structure Step (G H : ℝ → ℝ) : Prop where
  continuous : ContinuousOn G (Ici 0)
  derivative : ∀ s > 0, HasDerivAt G (-Real.pi * H s) s
  decay : Tendsto G atTop (𝓝 0)
  slice : ∀ a ≥ (0 : ℝ), IntegrableOn (fun r : ℝ => r * H (a + r^2)) (Ioi 0)

theorem Step.marginal {G H : ℝ → ℝ} (h : Step G H) (a : ℝ) (ha : 0 ≤ a) :
    (∫ v : E 2, H (a + ‖v‖ ^ 2)) = G a := by
  rw [plane_integral, planar_sq_profile_integral]
  have hc : ContinuousOn (fun r : ℝ => -G (a + r^2)) (Ici 0) :=
    (h.continuous.comp (by fun_prop) (fun r _ => add_nonneg ha (sq_nonneg r))).neg
  have hd (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) : HasDerivAt (fun t : ℝ => -G (a + t^2))
      ((2 * Real.pi) * (r * H (a + r^2))) r := by
    have hq : HasDerivAt (fun t : ℝ => a + t^2) (2*r) r := by
      simpa using ((hasDerivAt_id r).pow 2).const_add a
    convert ((h.derivative _ (add_pos_of_nonneg_of_pos ha (pow_pos hr 2))).comp r hq).neg using 1
    · rfl
    · ring
  have htop : Tendsto (fun r : ℝ => a + r^2) atTop atTop :=
    Filter.tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by decide : 2 ≠ 0))
  have hl : Tendsto (fun r : ℝ => -G (a+r^2)) atTop (𝓝 0) := by
    simpa using (h.decay.comp htop).neg
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto (hc 0 self_mem_Ici) hd
    ((h.slice a ha).const_mul (2 * Real.pi)) hl
  simpa [integral_const_mul] using hi

/-- A dimension lift consists of one Fubini reduction and an orthogonal rotation. -/
theorem lift {n : ℕ} [NeZero n] {F G H : ℝ → ℝ}
    (hrep : ∀ x : E n, transform G x = F ‖x‖)
    (h : Step G H) (hI : Integrable (fun k : E (n+2) => H (‖k‖ ^ 2))) :
    ∀ x : E (n+2), transform H x = F ‖x‖ := by
  intro x
  let y : E n := EuclideanSpace.single 0 ‖x‖
  have hy : ‖y‖ = ‖x‖ := by simp [y, EuclideanSpace.single, PiLp.norm_single]
  calc
    transform H x = transform H (embed y) :=
      transform_eq_of_norm_eq H (by rw [norm_embed, hy])
    _ = transform G y := transform_embed H G y hI h.marginal
    _ = F ‖x‖ := by rw [hrep, hy]

/-- A one-dimensional cosine identity in the usual real variable is enough
to start the Euclidean walk. Only nonnegative frequencies are needed. -/
theorem base {F G : ℝ → ℝ}
    (h : ∀ t ≥ (0 : ℝ), (∫ s : ℝ, G (s^2) * Real.cos (s*t)) = F t) :
    ∀ x : E 1, transform G x = F ‖x‖ := by
  intro x
  let y : E 1 := EuclideanSpace.single 0 ‖x‖
  have hy : ‖y‖ = ‖x‖ := by simp [y, EuclideanSpace.single, PiLp.norm_single]
  rw [transform_eq_of_norm_eq G hy.symm, ← h _ (norm_nonneg x)]
  let e : E 1 ≃ᵐ ℝ := (MeasurableEquiv.toLp 2 _).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have hv : MeasurePreserving e := (volume_preserving_funUnique (Fin 1) ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))
  unfold transform
  rw [← hv.integral_comp' (fun s => G (s^2) * Real.cos (s*‖x‖))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun k => by
    change G (‖k‖ ^ 2) * _ = G ((k 0)^2) * Real.cos (k 0 * ‖x‖)
    simp [EuclideanSpace.real_norm_sq_eq, y, EuclideanSpace.inner_single_right, mul_comm]

theorem transform_nine {F : ℝ → ℝ} (G : ℕ → ℝ → ℝ)
    (hbase : ∀ t ≥ (0 : ℝ), (∫ s : ℝ, G 0 (s^2) * Real.cos (s*t)) = F t)
    (hstep : ∀ j < 4, Step (G j) (G (j+1)))
    (hI : ∀ j < 4, Integrable (fun k : E (2*j+3) => G (j+1) (‖k‖ ^ 2))) :
    ∀ x : E 9, transform (G 4) x = F ‖x‖ := by
  have h1 := base hbase
  have h3 := lift h1 (hstep 0 (by decide)) (hI 0 (by decide))
  have h5 := lift h3 (hstep 1 (by decide)) (hI 1 (by decide))
  have h7 := lift h5 (hstep 2 (by decide)) (hI 2 (by decide))
  exact lift h7 (hstep 3 (by decide)) (hI 3 (by decide))

end GenesisD9Fourier

#print axioms GenesisD9Fourier.transform_eq_of_norm_eq
#print axioms GenesisD9Fourier.transform_embed
#print axioms GenesisD9Fourier.Step.marginal
#print axioms GenesisD9Fourier.transform_nine

namespace GenesisD9Fourier
open Filter Set
open scoped Topology

/-- The middle Arb certificate evaluates this ordinary-derivative expression. -/
def numerator (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  r^3 * iteratedDeriv 4 f r - 6*r^2 * iteratedDeriv 3 f r +
    15*r * iteratedDeriv 2 f r - 15 * deriv f r

/-- The scalar dimension recurrence identifies this numerator with the
fourth lifted profile, including all four angular Fourier factors. -/
theorem numerator_walk (G : ℕ → ℝ → ℝ) (hs : ∀ j < 4, Step (G j) (G (j+1)))
    {r : ℝ} (hr : 0 < r) :
    numerator (fun t => G 0 (t^2)) r = r^7 * ((2*Real.pi)^4 * G 4 (r^2)) := by
  let a : ℝ := -2 * Real.pi
  let f (j : ℕ) (t : ℝ) := G j (t^2)
  have hd (j : ℕ) (hj : j < 4) (t : ℝ) (ht : 0 < t) :
      HasDerivAt (f j) (a*t*f (j+1) t) t := by
    have hq : HasDerivAt (fun u : ℝ => u^2) (2*t) t := by simpa using hasDerivAt_pow 2 t
    convert ((hs j hj).derivative _ (pow_pos ht 2)).comp (h := fun u : ℝ => u^2) t hq using 1
    · rfl
    · dsimp [a, f]; ring
  have id1 (t : ℝ) (ht : 0 < t) : deriv (f 0) t = a*t*f 1 t := (hd 0 (by decide) t ht).deriv
  have transfer {p q : ℝ → ℝ} (he : ∀ t > 0, p t = q t) {t : ℝ} (ht : 0 < t) :
      deriv p t = deriv q t := (Filter.EventuallyEq.deriv_eq
        (Filter.mem_of_superset (Ioi_mem_nhds ht) (fun u hu => he u hu)))
  have id2 (t : ℝ) (ht : 0 < t) :
      iteratedDeriv 2 (f 0) t = a*f 1 t + a^2*t^2*f 2 t := by
    rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one, transfer id1 ht]
    have h := (((hasDerivAt_id t).const_mul a).mul (hd 1 (by decide) t ht)).deriv
    convert h using 1 <;> first | rfl | (dsimp; ring)
  have id3 (t : ℝ) (ht : 0 < t) :
      iteratedDeriv 3 (f 0) t = 3*a^2*t*f 2 t + a^3*t^3*f 3 t := by
    rw [iteratedDeriv_succ (n := 2), transfer id2 ht]
    have h := (((hd 1 (by decide) t ht).const_mul a).add
      ((((hasDerivAt_id t).pow 2).const_mul (a^2)).mul (hd 2 (by decide) t ht))).deriv
    convert h using 1 <;> first | rfl | (dsimp; ring)
  have id4 : iteratedDeriv 4 (f 0) r =
      3*a^2*f 2 r + 6*a^3*r^2*f 3 r + a^4*r^4*f 4 r := by
    rw [iteratedDeriv_succ (n := 3), transfer id3 hr]
    have h := ((((hasDerivAt_id r).const_mul (3*a^2)).mul (hd 2 (by decide) r hr)).add
      ((((hasDerivAt_id r).pow 3).const_mul (a^3)).mul (hd 3 (by decide) r hr))).deriv
    convert h using 1 <;> first | rfl | (dsimp; ring)
  change numerator (f 0) r = _
  rw [numerator, id4, id3 r hr, id2 r hr, id1 r hr]
  dsimp [a, f]; ring

end GenesisD9Fourier

#print axioms GenesisD9Fourier.numerator_walk

namespace GenesisD9Fourier
open Set
/-- A function vanishing at zero with positive derivative on (0,b)
is positive up to and including the right endpoint. -/
private theorem positive_from_zero {f : ℝ → ℝ} {b : ℝ}
    (hc : Continuous f) (hz : f 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, 0 < deriv f t) :
    ∀ t ∈ Ioc 0 b, 0 < f t := by
  have hm := strictMonoOn_of_deriv_pos (convex_Icc 0 b) hc.continuousOn (by
    rwa [interior_Icc])
  intro t ht
  simpa [hz] using hm (left_mem_Icc.mpr (ht.1.le.trans ht.2)) ⟨ht.1.le, ht.2⟩ ht.1

/-- Positive eighth derivative and the four vanishing odd jets at zero imply
positivity of the Arb numerator at every positive radius through b. -/
theorem near_numerator_pos (p : ℕ → ℝ → ℝ) {b : ℝ}
    (hc : ∀ j < 8, Continuous (p j))
    (hd : ∀ j < 8, ∀ t : ℝ, HasDerivAt (p j) (p (j+1) t) t)
    (h1 : p 1 0 = 0) (h3 : p 3 0 = 0) (h5 : p 5 0 = 0) (h7 : p 7 0 = 0)
    (h8 : ∀ t ∈ Ioo 0 b, 0 < p 8 t) :
    ∀ t ∈ Ioc 0 b, 0 < t^3 * p 4 t - 6*t^2 * p 3 t + 15*t * p 2 t - 15*p 1 t := by
  have hp7 := positive_from_zero (hc 7 (by decide)) h7
    (fun t ht => (hd 7 (by decide) t).deriv.symm ▸ h8 t ht)
  let L (t : ℝ) := t*p 6 t - p 5 t
  let M (t : ℝ) := t^2*p 5 t - 3*t*p 4 t + 3*p 3 t
  let N (t : ℝ) := t^3*p 4 t - 6*t^2*p 3 t + 15*t*p 2 t - 15*p 1 t
  have hpL : ∀ t ∈ Ioc 0 b, 0 < L t := by
    apply positive_from_zero (continuous_id.mul (hc 6 (by decide)) |>.sub (hc 5 (by decide)))
      (by simp [h5])
    intro t ht
    have hh := (((hasDerivAt_id t).mul (hd 6 (by decide) t)).sub (hd 5 (by decide) t)).deriv
    change deriv L t = _ at hh
    change 0 < deriv L t
    calc
      0 < t*p 7 t := mul_pos ht.1 (hp7 t ⟨ht.1, ht.2.le⟩)
      _ = _ := by rw [hh]; dsimp; ring
  have hpM : ∀ t ∈ Ioc 0 b, 0 < M t := by
    apply positive_from_zero ((((continuous_id.pow 2).mul (hc 5 (by decide))).sub
      ((continuous_const.mul continuous_id).mul (hc 4 (by decide)))).add
      (continuous_const.mul (hc 3 (by decide)))) (by simp [h3])
    intro t ht
    have hh := (((((hasDerivAt_id t).pow 2).mul (hd 5 (by decide) t)).sub
      (((hasDerivAt_id t).const_mul 3).mul (hd 4 (by decide) t))).add
      ((hd 3 (by decide) t).const_mul 3)).deriv
    change deriv M t = _ at hh
    change 0 < deriv M t
    calc
      0 < t*L t := mul_pos ht.1 (hpL t ⟨ht.1, ht.2.le⟩)
      _ = _ := by rw [hh]; dsimp [L]; ring
  apply positive_from_zero (f := N) (((((continuous_id.pow 3).mul (hc 4 (by decide))).sub
    ((continuous_const.mul (continuous_id.pow 2)).mul (hc 3 (by decide)))).add
    ((continuous_const.mul continuous_id).mul (hc 2 (by decide)))).sub
    (continuous_const.mul (hc 1 (by decide)))) (by simp [N, h1])
  intro t ht
  have hh := (((((((hasDerivAt_id t).pow 3).mul (hd 4 (by decide) t)).sub
    ((((hasDerivAt_id t).pow 2).const_mul 6).mul (hd 3 (by decide) t))).add
    (((hasDerivAt_id t).const_mul 15).mul (hd 2 (by decide) t))).sub
    ((hd 1 (by decide) t).const_mul 15))).deriv
  change deriv N t = _ at hh
  calc
    0 < t*M t := mul_pos ht.1 (hpM t ⟨ht.1, ht.2.le⟩)
    _ = _ := by rw [hh]; dsimp [M]; ring

end GenesisD9Fourier
#print axioms GenesisD9Fourier.near_numerator_pos
