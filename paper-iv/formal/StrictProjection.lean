import measure_theory.constructions.prod.integral
import tactic.linarith

/- Lean 3.51.1 and mathlib3 at 65a1391a0106c9204fe45bc73a039f056558cb83. -/

open measure_theory set function filter
open_locale measure_theory

namespace xi_projection

variables {α β : Type*} [measurable_space α] [measurable_space β]

/-- A nonnegative integrable gap with a positive-mass strict witness has positive integral.
    No measurability of the witness set or finiteness of the ambient measure is required. -/
theorem integral_pos_of_witness {μ : measure α} {gap : α → ℝ} {S : set α}
    (hi : integrable gap μ) (hn : 0 ≤ᵐ[μ] gap)
    (hm : 0 < μ S) (hs : ∀ x ∈ S, 0 < gap x) :
    0 < ∫ x, gap x ∂μ :=
begin
  apply (integral_pos_iff_support_of_nonneg_ae hn hi).2,
  exact lt_of_lt_of_le hm (measure_mono (λ x hx, (hs x hx).ne')),
end

/-- Integrating preserves a strict inequality witnessed on a set of positive measure. -/
theorem integral_lt_of_witness {μ : measure α} {f g : α → ℝ} {S : set α}
    (hf : integrable f μ) (hg : integrable g μ) (hle : f ≤ᵐ[μ] g)
    (hm : 0 < μ S) (hs : ∀ x ∈ S, f x < g x) :
    (∫ x, f x ∂μ) < ∫ x, g x ∂μ :=
begin
  have hn : 0 ≤ᵐ[μ] (λ x, g x - f x) :=
    hle.mono (λ x hx, sub_nonneg.mpr hx),
  have hp := integral_pos_of_witness (hg.sub hf) hn hm
    (λ x hx, sub_pos.mpr (hs x hx)),
  simpa only [pi.sub_apply, integral_sub hg hf, sub_pos] using hp,
end

/-- Positive mass of each sign forces strictness in the real integral triangle inequality. -/
theorem abs_integral_lt_integral_abs {μ : measure α} {f : α → ℝ}
    (hf : integrable f μ) (hp : 0 < μ {x | 0 < f x}) (hn : 0 < μ {x | f x < 0}) :
    |∫ x, f x ∂μ| < ∫ x, |f x| ∂μ :=
begin
  have ha : integrable (λ x, |f x|) μ := by simpa only [real.norm_eq_abs] using hf.norm,
  have upper := integral_lt_of_witness hf ha (eventually_of_forall (λ x, le_abs_self (f x)))
    hn (λ x (hx : f x < 0), by { change f x < |f x|, rw [abs_of_neg hx], linarith }),
  have lower := integral_lt_of_witness hf.neg ha
    (eventually_of_forall (λ x, neg_le_abs_self (f x)))
    hp (λ x (hx : 0 < f x), by { change -f x < |f x|, rw [abs_of_pos hx], linarith }),
  change (∫ x, -f x ∂μ) < ∫ x, |f x| ∂μ at lower,
  rw [integral_neg] at lower,
  exact abs_lt.mpr ⟨by linarith, upper⟩,
end

/-- The nested integral step for adjacent dimension envelopes. The inner variable is the
    projection length and the outer variable is the original radial frequency. -/
theorem strict_projection_envelope {ν : measure α} {κ : measure β}
    (A : α → β → ℝ) {S : set α}
    (inner : ∀ r, integrable (A r) κ)
    (lower_int : integrable (λ r, |∫ b, A r b ∂κ|) ν)
    (upper_int : integrable (λ r, ∫ b, |A r b| ∂κ) ν)
    (hm : 0 < ν S)
    (both : ∀ r ∈ S, 0 < κ {b | 0 < A r b} ∧ 0 < κ {b | A r b < 0}) :
    (∫ r, |∫ b, A r b ∂κ| ∂ν) < ∫ r, (∫ b, |A r b| ∂κ) ∂ν :=
begin
  refine integral_lt_of_witness lower_int upper_int _ hm _,
  { apply eventually_of_forall,
    intro r,
    simpa only [real.norm_eq_abs] using (@norm_integral_le_integral_norm β ℝ _ _ _ _ κ (A r)) },
  { intros r hr,
    exact abs_integral_lt_integral_abs (inner r) (both r hr).1 (both r hr).2 },
end

/-- A continuous sign-changing kernel gives positive mass of each sign after scaling.
    The projection length law charges every nonempty open subset of the unit interval. -/
theorem angular_both_signs (κ : measure ℝ)
    (full : ∀ U : set ℝ, is_open U → U.nonempty → U ⊆ Ioo 0 1 → 0 < κ U)
    {Ω : ℝ → ℝ} (hc : continuous Ω)
    {p n z : ℝ} (hp : 0 < p) (hn : 0 < n) (hpz : p < z) (hnz : n < z)
    (hpos : 0 < Ω p) (hneg : Ω n < 0) :
    0 < κ {b | 0 < Ω (z*b)} ∧ 0 < κ {b | Ω (z*b) < 0} :=
begin
  have hz : 0 < z := lt_trans hp hpz,
  have cont : continuous (λ b : ℝ, Ω (z*b)) := hc.comp (continuous_const.mul continuous_id),
  have within : ∀ t : ℝ, 0 < t → t < z → t/z ∈ Ioo (0:ℝ) 1 :=
    λ t ht htz, ⟨div_pos ht hz, (div_lt_one hz).mpr htz⟩,
  have mass : ∀ (U : set ℝ), is_open U → (Ioo 0 1 ∩ U).nonempty → 0 < κ U :=
    λ U hu hne, lt_of_lt_of_le (full _ (is_open_Ioo.inter hu) hne (inter_subset_left _ _))
      (measure_mono (inter_subset_right _ _)),
  split,
  { apply mass _ (is_open_lt continuous_const cont),
    exact ⟨p/z, within p hp hpz, by simpa only [mem_set_of_eq, mul_div_cancel' p hz.ne'] using hpos⟩ },
  { apply mass _ (is_open_lt cont continuous_const),
    exact ⟨n/z, within n hn hnz, by simpa only [mem_set_of_eq, mul_div_cancel' n hz.ne'] using hneg⟩ },
end

/-- A strict radial projection bound at every positive separation for every continuous
    kernel that takes both signs on positive arguments. The radius law charges every
    upper tail and the projection length law charges every open subset of (0,1). -/
theorem strict_radial_projection (ν κ : measure ℝ)
    (tail : ∀ t : ℝ, 0 < ν (Ioi t))
    (full : ∀ U : set ℝ, is_open U → U.nonempty → U ⊆ Ioo 0 1 → 0 < κ U)
    {Ω : ℝ → ℝ} (hc : continuous Ω)
    {p n : ℝ} (hp : 0 < p) (hn : 0 < n) (hpos : 0 < Ω p) (hneg : Ω n < 0)
    {a : ℝ} (ha : 0 < a)
    (inner : ∀ r : ℝ, integrable (λ b : ℝ, Ω ((a*r)*b)) κ)
    (lower_int : integrable (λ r : ℝ, |∫ b, Ω ((a*r)*b) ∂κ|) ν)
    (upper_int : integrable (λ r : ℝ, ∫ b, |Ω ((a*r)*b)| ∂κ) ν) :
    (∫ r, |∫ b, Ω ((a*r)*b) ∂κ| ∂ν) < ∫ r, (∫ b, |Ω ((a*r)*b)| ∂κ) ∂ν :=
begin
  apply strict_projection_envelope (λ r b : ℝ, Ω ((a*r)*b))
    inner lower_int upper_int (tail (max p n / a)),
  intros r hr,
  have hlt : max p n < a*r := by simpa only [mul_comm r a] using (div_lt_iff ha).1 hr,
  exact angular_both_signs κ full hc hp hn
    (lt_of_le_of_lt (le_max_left _ _) hlt) (lt_of_le_of_lt (le_max_right _ _) hlt) hpos hneg,
end

/-- Discharge all integrability conditions for finite laws and bounded continuous kernels. -/
theorem strict_bounded_radial_projection (ν κ : measure ℝ)
    [is_finite_measure ν] [is_finite_measure κ]
    (tail : ∀ t : ℝ, 0 < ν (Ioi t))
    (full : ∀ U : set ℝ, is_open U → U.nonempty → U ⊆ Ioo 0 1 → 0 < κ U)
    {Ω : ℝ → ℝ} (hc : continuous Ω) (bounded : ∀ t : ℝ, |Ω t| ≤ 1)
    {p n : ℝ} (hp : 0 < p) (hn : 0 < n) (hpos : 0 < Ω p) (hneg : Ω n < 0)
    {a : ℝ} (ha : 0 < a) :
    (∫ r, |∫ b, Ω ((a*r)*b) ∂κ| ∂ν) < ∫ r, (∫ b, |Ω ((a*r)*b)| ∂κ) ∂ν :=
begin
  let F : ℝ × ℝ → ℝ := λ v, Ω ((a * v.1) * v.2),
  have hcF : continuous F := hc.comp ((continuous_const.mul continuous_fst).mul continuous_snd),
  have hprod : integrable F (ν.prod κ) :=
    (integrable_const (1:ℝ)).mono' hcF.ae_strongly_measurable
      (eventually_of_forall (λ v, by simpa only [real.norm_eq_abs] using bounded ((a*v.1)*v.2))),
  apply strict_radial_projection ν κ tail full hc hp hn hpos hneg ha,
  { intro r,
    have hcR : continuous (λ b : ℝ, Ω ((a*r)*b)) := hc.comp (continuous_const.mul continuous_id),
    exact (integrable_const (1:ℝ)).mono' hcR.ae_strongly_measurable
      (eventually_of_forall (λ b, by simpa only [real.norm_eq_abs] using bounded ((a*r)*b))) },
  { exact hprod.integral_prod_left.abs },
  { simpa only [real.norm_eq_abs] using hprod.integral_norm_prod_left },
end

/-- The adjacent-dimension envelope inequality, assuming the angular kernel identity
    and the product pushforward for the radial law. All integrability, the Fubini step,
    and the change of variables are part of the proof. -/
theorem adjacent_envelopes_of_projection (ν κ μ : measure ℝ)
    [is_finite_measure ν] [is_finite_measure κ]
    (tail : ∀ t : ℝ, 0 < ν (Ioi t))
    (full : ∀ U : set ℝ, is_open U → U.nonempty → U ⊆ Ioo 0 1 → 0 < κ U)
    {Ω Ψ : ℝ → ℝ} (hc : continuous Ω) (bounded : ∀ t : ℝ, |Ω t| ≤ 1)
    {p n : ℝ} (hp : 0 < p) (hn : 0 < n) (hpos : 0 < Ω p) (hneg : Ω n < 0)
    (hkernel : ∀ z, Ψ z = ∫ b, Ω (z*b) ∂κ)
    (hradius : μ = measure.map (λ v : ℝ × ℝ, v.1 * v.2) (ν.prod κ))
    {a : ℝ} (ha : 0 < a) :
    (∫ r, |Ψ (a*r)| ∂ν) < ∫ s, |Ω (a*s)| ∂μ :=
begin
  let m : ℝ × ℝ → ℝ := λ v, v.1*v.2,
  let g : ℝ → ℝ := λ s, |Ω (a*s)|,
  have hcm : continuous m := continuous_fst.mul continuous_snd,
  have hcg : continuous g := (hc.comp (continuous_const.mul continuous_id)).abs,
  have hi : integrable (g ∘ m) (ν.prod κ) :=
    (integrable_const (1:ℝ)).mono' (hcg.comp hcm).ae_strongly_measurable
      (eventually_of_forall (λ v, by simpa only [function.comp_apply, g, real.norm_eq_abs, abs_abs]
        using bounded (a*m v))),
  have heq : (∫ s, g s ∂μ) = ∫ r, (∫ b, |Ω ((a*r)*b)| ∂κ) ∂ν,
  { rw [hradius, integral_map_of_strongly_measurable hcm.measurable hcg.strongly_measurable],
    simpa only [function.comp_apply, m, g, mul_assoc] using integral_prod (g ∘ m) hi },
  change (∫ r, |Ψ (a*r)| ∂ν) < ∫ s, g s ∂μ,
  simp only [hkernel, heq],
  exact strict_bounded_radial_projection ν κ tail full hc bounded hp hn hpos hneg ha,
end

#check integral_pos_of_witness
#print axioms integral_pos_of_witness
#check integral_lt_of_witness
#print axioms integral_lt_of_witness
#check abs_integral_lt_integral_abs
#print axioms abs_integral_lt_integral_abs
#check strict_projection_envelope
#print axioms strict_projection_envelope

#check angular_both_signs
#print axioms angular_both_signs
#check strict_radial_projection
#print axioms strict_radial_projection

#check strict_bounded_radial_projection
#print axioms strict_bounded_radial_projection

#check adjacent_envelopes_of_projection
#print axioms adjacent_envelopes_of_projection

end xi_projection
