import D9Fourier

noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace GenesisD9Fourier

/-- A positive upper-dimensional radial profile gives the lower-dimensional
profile by integration, away from the null central slice. -/
structure OpenStep (G H : ℝ → ℝ) : Prop where
  derivative : ∀ s > 0, HasDerivAt G (-Real.pi * H s) s
  decay : Tendsto G atTop (𝓝 0)

theorem OpenStep.pos {G H : ℝ → ℝ} (h : OpenStep G H) (hh : ∀ s > 0, 0 < H s) :
    ∀ s > 0, 0 < G s := by
  have anti : StrictAntiOn G (Ioi 0) := strictAntiOn_of_deriv_neg (convex_Ioi _)
    (fun x hx => (h.derivative x hx).continuousAt.continuousWithinAt) (by
      rw [isOpen_Ioi.interior_eq]
      intro x hx
      rw [(h.derivative _ hx).deriv]
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (hh _ hx))
  intro s hs
  have h' : s + 1 ∈ Ioi (0:ℝ) := by change 0 < s+1; linarith
  have hh' : 0 ≤ G (s+1) := le_of_tendsto h.decay (by
    filter_upwards [eventually_gt_atTop (s+1)] with x hx
    exact (anti h' (lt_trans h' hx) hx).le)
  exact hh'.trans_lt (anti hs h' (by linarith))

theorem OpenStep.marginal {G H : ℝ → ℝ} (h : OpenStep G H) (hh : ∀ s > 0, 0 < H s)
    {a : ℝ} (ha : 0 < a) : (∫ v : E 2, H (a + ‖v‖^2)) = G a := by
  rw [plane_integral, planar_sq_profile_integral]
  have hd (r : ℝ) : HasDerivAt (fun t : ℝ => -G (a+t^2))
      ((2*Real.pi)*(r*H (a+r^2))) r := by
    have hq : HasDerivAt (fun t : ℝ => a+t^2) (2*r) r := by
      simpa using ((hasDerivAt_id r).pow 2).const_add a
    convert ((h.derivative _ (add_pos_of_pos_of_nonneg ha (sq_nonneg r))).comp r hq).neg using 1
    · rfl
    · ring
  have htop : Tendsto (fun r : ℝ => a+r^2) atTop atTop :=
    Filter.tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by decide : 2 ≠ 0))
  have hl : Tendsto (fun r : ℝ => -G (a+r^2)) atTop (𝓝 0) := by simpa using (h.decay.comp htop).neg
  have hi := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (fun r _ => hd r)
    (fun r hr => mul_nonneg (by positivity)
      (mul_nonneg (le_of_lt hr) (hh _ (add_pos_of_pos_of_nonneg ha (sq_nonneg r))).le)) hl
  simpa [integral_const_mul] using hi

/-- Positivity, a finite marginal, and Fubini propagate both integrability and
the cosine-transform identity. The value assigned at the origin is immaterial. -/
theorem lift_positive {n : ℕ} [NeZero n] {F G H : ℝ → ℝ}
    (hG : Integrable (fun k : E n => G (‖k‖^2))) (hm : Measurable H)
    (hpos : ∀ s > 0, 0 < H s) (hs : OpenStep G H)
    (hrep : ∀ x : E n, transform G x = F ‖x‖) :
    Integrable (fun k : E (n+2) => H (‖k‖^2)) ∧
      ∀ x : E (n+2), transform H x = F ‖x‖ := by
  let f := fun p : E n × E 2 => H (‖p.1‖^2+‖p.2‖^2)
  have hn (k : E (n+2)) : ‖k‖^2 =
      ‖(splitMeas n k).1‖^2+‖(splitMeas n k).2‖^2 := by
    rw [← (split n).norm_map k]
    exact WithLp.prod_norm_sq_eq_of_L2 _
  have hz : ∀ᵐ u : E n ∂volume, u ≠ 0 := volume.ae_ne 0
  have hf : Integrable f := by
    rw [Measure.volume_eq_prod]
    apply (integrable_prod_iff ((hm.comp (by fun_prop)).aestronglyMeasurable :
      AEStronglyMeasurable f (volume.prod volume))).mpr
    constructor
    · filter_upwards [hz] with u hu
      have hp := sq_pos_of_pos (norm_pos_iff.mpr hu)
      by_contra hni
      have q := hs.marginal hpos hp
      rw [show (∫ v : E 2, H (‖u‖^2+‖v‖^2)) = 0 from integral_undef hni] at q
      exact (hs.pos hpos _ hp).ne' q.symm
    · apply hG.congr
      filter_upwards [hz] with u hu
      have hp := sq_pos_of_pos (norm_pos_iff.mpr hu)
      rw [← hs.marginal hpos hp]
      apply integral_congr_ae
      filter_upwards with v
      exact (abs_of_pos (hpos _ (add_pos_of_pos_of_nonneg hp (sq_nonneg ‖v‖)))).symm
  have hi := ((split_preserves n).integrable_comp_emb (splitMeas n).measurableEmbedding).mpr hf
  refine ⟨by simpa only [Function.comp_def, f, ← hn] using hi, ?_⟩
  intro x
  let y : E n := EuclideanSpace.single 0 ‖x‖
  have hy : ‖y‖ = ‖x‖ := by simp [y, EuclideanSpace.single, PiLp.norm_single]
  rw [transform_eq_of_norm_eq H (y := embed y) (by rw [norm_embed, hy]), ← hy, ← hrep]
  let w := fun p : E n × E 2 => f p * Real.cos ⟪p.1,y⟫_ℝ
  have hw : Integrable w := hf.mul_bdd (c := 1) (by fun_prop)
    (ae_of_all _ fun _ => Real.abs_cos_le_one _)
  have hinner (k : E (n+2)) : ⟪k, embed y⟫_ℝ = ⟪(splitMeas n k).1, y⟫_ℝ := by
    rw [← (split n).inner_map_map k (embed y)]
    simp [embed, WithLp.prod_inner_apply, splitMeas]
  calc
    transform H (embed y) = ∫ k, w (splitMeas n k) := by
      apply integral_congr_ae; filter_upwards with k
      simp [w, f, hn k, hinner k]
    _ = ∫ p, w p := (split_preserves n).integral_comp' _
    _ = ∫ u : E n, ∫ v : E 2, w (u,v) := integral_prod _ hw
    _ = transform G y := by
      apply integral_congr_ae
      filter_upwards [hz] with u hu
      simp only [w, f, integral_mul_const, hs.marginal hpos (sq_pos_of_pos (norm_pos_iff.mpr hu))]

end GenesisD9Fourier
