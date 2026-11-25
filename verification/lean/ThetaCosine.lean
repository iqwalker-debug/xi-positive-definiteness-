import ThetaSeries

noncomputable section
open Filter Set MeasureTheory Polynomial HurwitzZeta
open scoped Topology
namespace GenesisTidalMellin

def phiPoly : ℝ[X] := X * (2*X-3)

abbrev g := thetaSeries 1
abbrev phi := thetaSeries phiPoly

theorem thetaSeries_integrableOn (P : ℝ[X]) : IntegrableOn (thetaSeries P) (Ioi 0) := by
  obtain ⟨C,hC,h⟩ := thetaSeries_decay_bound P
  have hc : ContinuousOn (thetaSeries P) (Ioi (0:ℝ)) := fun r hr =>
    (hasDerivAt_thetaSeries P (by change 0 < r at hr; linarith)).continuousAt.continuousWithinAt
  refine ((integrableOn_exp_neg_Ioi 0).const_mul C).mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  exact h x (by change 0 < x at hx; linarith)

theorem thetaSeries_mul_tendsto (P : ℝ[X]) {b : ℝ → ℝ} (hb : ∀ x, ‖b x‖ ≤ 1) :
    Tendsto (fun r => thetaSeries P r * b r) atTop (𝓝 0) := by
  obtain ⟨C,_,h⟩ := thetaSeries_decay_bound P
  apply squeeze_zero_norm' (a := fun r => C * Real.exp (-r))
  · filter_upwards [eventually_gt_atTop (-(1/8:ℝ))] with x hx
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hb x)).trans (h _ hx)
  · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C

theorem evenKernel_log (r : ℝ) :
    Real.exp (r/2) * evenKernel 0 (Real.exp (2*r)) = Real.exp (r/2) + 2*g r := by
  have h := (hasSum_nat_cosKernel₀ 0 (Real.exp_pos (2*r))).tsum_eq
  have h' : (∑' n : ℕ, 2 * Real.exp (-Real.pi * ((n:ℝ)+1)^2 * Real.exp (2*r))) =
      evenKernel 0 (Real.exp (2*r)) - 1 := by simpa [evenKernel_eq_cosKernel_of_zero] using h
  have h2 : Real.exp (r/2) * (evenKernel 0 (Real.exp (2*r))-1) = 2 * g r := by
    rw [← h']
    simp only [g, thetaSeries, weightedTerm, Polynomial.eval_one, mul_one, thetaTerm, thetaX,
      sub_eq_add_neg, Real.exp_add, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [neg_mul]
    ring
  linarith

theorem fullTheta_even : Function.Even (fun r : ℝ => Real.exp (r/2) + 2*g r) := by
  intro r
  change Real.exp (-r/2) + 2*g (-r) = Real.exp (r/2) + 2*g r
  rw [← evenKernel_log (-r), ← evenKernel_log r, evenKernel_functional_equation 0 (Real.exp (2*(-r))),
    ← evenKernel_eq_cosKernel_of_zero]
  have hi : 1 / Real.exp (2 * -r) = Real.exp (2*r) := by rw [mul_neg, Real.exp_neg]; simp
  rw [hi, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, one_div, ← Real.exp_neg,
    ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem g'_zero : thetaSeries (thetaStep 1) 0 = -1/4 := by
  let f := fun r : ℝ => Real.exp (r/2) + 2*g r
  let D := 1/2 + 2*thetaSeries (thetaStep 1) 0
  have h : HasDerivAt f D 0 := by
    have he : HasDerivAt (fun r : ℝ => Real.exp (r/2)) (1/2) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).div_const 2).exp
    exact he.add ((hasDerivAt_thetaSeries 1 (r := 0) (by norm_num)).const_mul 2)
  have hn : HasDerivAt (fun r : ℝ => f (-r)) (-D) 0 := by
    change HasDerivAt (f ∘ Neg.neg) (-D) 0
    simpa using (show HasDerivAt f D (-(0:ℝ)) by simpa using h).comp 0 (hasDerivAt_neg (x := (0:ℝ)))
  rw [show (fun r : ℝ => f (-r)) = f from funext fullTheta_even] at hn
  have hd := hn.unique h
  dsimp [D] at hd
  linarith

theorem ode_theta {r : ℝ} (hr : 0 ≤ r) :
    thetaSeries (thetaStep (thetaStep 1)) r - g r / 4 = 2 * phi r := by
  have hh : -(1/8:ℝ) < r := by linarith
  have htt (n : ℕ) : weightedTerm (thetaStep (thetaStep 1)) n r =
      (1/4:ℝ) * weightedTerm 1 n r + 2 * weightedTerm phiPoly n r := by
    simp [thetaStep, weightedTerm, phiPoly, Polynomial.derivative_mul]
    ring
  change (∑' n, weightedTerm (thetaStep (thetaStep 1)) n r) - (∑' n, weightedTerm 1 n r)/4 = 2 * ∑' n, weightedTerm phiPoly n r
  simp_rw [htt]
  rw [Summable.tsum_add ((summable_weightedTerm 1 hh).mul_left _)
    ((summable_weightedTerm phiPoly hh).mul_left _), tsum_mul_left, tsum_mul_left]
  ring

theorem thetaSeries_cos_integrable (P : ℝ[X]) (t : ℝ) :
    IntegrableOn (fun r => thetaSeries P r * Real.cos (t*r)) (Ioi 0) :=
  (thetaSeries_integrableOn P).mul_bdd (c := 1) (by fun_prop)
    (ae_of_all _ fun _ => Real.abs_cos_le_one _)

theorem phi_ibp (t : ℝ) :
    4 * (∫ r in Ioi (0:ℝ), phi r * Real.cos (t*r)) =
    1/2 - 2*(t^2+1/4) * (∫ r in Ioi (0:ℝ), g r * Real.cos (t*r)) := by
  apply theta_cosine_ibp t g (thetaSeries (thetaStep 1)) (thetaSeries (thetaStep (thetaStep 1)))
  · exact fun r hr => hasDerivAt_thetaSeries 1 (by linarith)
  · exact fun r hr => hasDerivAt_thetaSeries _ (by linarith)
  · exact fun _ hr => ode_theta hr.le
  · exact g'_zero
  · have hc := thetaSeries_mul_tendsto (thetaStep 1) (b := fun r => Real.cos (t*r))
      (fun r => Real.abs_cos_le_one _)
    have hs := thetaSeries_mul_tendsto 1 (b := fun r => Real.sin (t*r))
      (fun r => Real.abs_sin_le_one _)
    simpa [mul_assoc] using hc.add (hs.const_mul t)
  · exact thetaSeries_cos_integrable _ _
  · exact thetaSeries_cos_integrable _ _

end GenesisTidalMellin

namespace GenesisTidalMellin
open Complex

private def wave (t r : ℝ) : ℂ := Complex.exp (((t*r:ℝ):ℂ)*I) * splitTheta r

private theorem split_pos {r : ℝ} (hr : 0 < r) : splitTheta r = ((2*g r:ℝ):ℂ) := by
  simpa [g,thetaSeries,weightedTerm,thetaTerm,thetaX] using splitTheta_pos_eq_tsum hr

private theorem wave_int (t : ℝ) : IntegrableOn (wave t) (Ioi 0) := by
  have hg : IntegrableOn (fun r => ((2*g r:ℝ):ℂ)) (Ioi 0) :=
    ((thetaSeries_integrableOn 1).const_mul 2).ofReal
  have h := hg.bdd_mul (f := fun r => Complex.exp (((t*r:ℝ):ℂ)*I)) (c := 1)
    (by fun_prop) (ae_of_all _ fun r => by simp [Complex.norm_exp_mul_I])
  exact IntegrableOn.congr_fun h (fun r hr => by simp [wave,split_pos (show 0 < r from hr)]) measurableSet_Ioi

private theorem wave_reflect (t r : ℝ) : wave t (-r) = wave (-t) r := by
  simp only [wave, splitTheta_even r, mul_neg, neg_mul]

theorem split_wave_eq_cosine (t : ℝ) :
    (∫ r, wave t r) = ((4 * ∫ r in Ioi (0:ℝ), g r * Real.cos (t*r) : ℝ):ℂ) := by
  have hpos := wave_int t
  have href : IntegrableOn (fun r => wave t (-r)) (Ioi 0) := by
    simpa only [wave_reflect] using wave_int (-t)
  have hneg : IntegrableOn (wave t) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simpa only [Function.comp_def, neg_preimage, neg_Iic, neg_zero] using
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi href)
  rw [← intervalIntegral.integral_Iic_add_Ioi hneg hpos,
    ← show (∫ r in Ioi (0:ℝ), wave t (-r)) = ∫ r in Iic 0, wave t r by
        simpa using integral_comp_neg_Ioi (0:ℝ) (wave t),
    ← integral_add href hpos]
  rw [← integral_const_mul, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change wave t (-r) + wave t r = _
  rw [wave_reflect, wave, wave, split_pos (show 0 < r from hr)]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [show (-t)*r = -(t*r) by ring, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- Fourier identification for the concrete critical-line completion and the
same infinite polynomial-weighted theta series as the numerical certificate. -/
theorem completedXi_eq_phi_cosine (t : ℝ) :
    (criticalPoint t * (criticalPoint t - 1) * completedRiemannZeta₀ (criticalPoint t) + 1) / 2 =
      ((4 * ∫ r in Ioi (0:ℝ), phi r * Real.cos (t*r) : ℝ):ℂ) := by
  rw [completedXi_critical_eq_splitTheta, phi_ibp]
  change 1/2 - _ * (∫ r, wave t r) = _
  rw [split_wave_eq_cosine]
  push_cast
  ring

end GenesisTidalMellin
#print axioms GenesisTidalMellin.completedXi_eq_phi_cosine
