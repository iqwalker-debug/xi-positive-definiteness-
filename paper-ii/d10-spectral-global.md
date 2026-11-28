# A computer-assisted characterization of the D10 heat endpoint

Write f_d(s) for the angular-frequency radial spectral density at a fixed heat parameter λ, and Z for its positive one-dimensional normalization. On the parameter interval J = [−0.398449, −0.398448], the D10 kernel is positive semidefinite exactly when f₁₀(0) ≥ 0. The endpoint E is the unique root in J of f₁₀(0) = 0. It obeys

    −0.398448207016 < E < −0.398448207015.

This argument uses the radial dimension walk, D9 admissibility and the all-dimensional downward-closure lemma in Paper II. The additional interval computations below were run in python-flint 0.8.0. This research note and the new analytic implications have not been checked in Lean.

## A sign criterion for the projection

At fixed λ, let h(r)=f₁₁(r). Fourier uniqueness identifies the D10 density with its marginal,
f₁₀(s)=2∫₀^∞ h(√(s²+t²)) dt. This holds also for signed Schwartz densities.

Suppose h is negative below a single radius c, increases on [0,c], and is positive above c. For 0 ≤ s ≤ c, split h into min(h,0) and max(h,0). The former is nondecreasing everywhere, so its marginal at s is at least its marginal at zero, pointwise in t. For the positive part change variables to r=√(s²+t²). Its marginal is 2∫ from c to infinity of h(r)r/√(r²−s²) dr, at least 2∫ from c to infinity of h(r) dr. Hence f₁₀(s) ≥ f₁₀(0) on [0,c]. For s ≥ c the integrand of the original marginal is positive for t>0. This proves the criterion, including equality at the endpoint. A negative origin value excludes positive semidefiniteness by continuity and Bochner uniqueness.

## Certifying the single sign change

Let x=r² and g(x)=exp(λx)Φ(√x). The dimension walk gives π⁵ Z h(r)=−g⁽⁵⁾(x). Uniformly for λ in J, interval arithmetic verifies its negative value at x=0, positive derivative −g⁽⁶⁾(x) on [0,1/16], and positive value on [1/16,1/4]. Taylor coefficients of g are obtained by convolution with the exponential series. Cauchy's inequality supplies the derivative remainder from the existing bound for Φ(√x) on |x|=3/5, enlarged by exp(|λ| 3/5).

For r≥1/2, the exact polynomial recurrence from the odd-dimensional certificate gives the sign of each theta summand. After the substitution r=1/2+z, X=(8539/1000)(1+2z+2z²)+u, the 104 nonzero coefficients are positive throughout J, including the constant term. Here z,u≥0 on the tail. The sign and derivative assertions give the required single radius c separately for every λ in J.

## Strict decrease of the scaled origin value

Write B_d(λ)=π^(d/2) Z f_d(0). Fourier inversion at zero gives B_d = [2^(1−d)/Γ(d/2)] ∫₀^∞ t^(d−1) U(t) dt, where U(t)=Z F_λ(t). Differentiating the heat weight yields ∂λ U=−U''. Differentiation and two integrations by parts are justified by uniform Schwartz bounds on compact λ-intervals (the theta density and its derivatives decay faster than Gaussians). The boundary terms vanish for d=10. Using the displayed constants gives B₁₀' = −(9/2)B₈.

Throughout J the D9 density is nonnegative by the existing D9 endpoint theorem. It is continuous, radial and has total mass one. Consequently f₈(0)=2∫₀^∞ f₉(t) dt is strictly positive. Thus B₁₀ decreases strictly on J. The contour enclosures establish opposite signs at the narrow bracket endpoints. The projection criterion, continuity, and downward closure give A₁₀=(−∞,E]. In particular the exact endpoint is admissible.

## Replay

On the research branch run the following from paper-ii with python-flint and sympy installed.

    python d10_spectral_global.py

The script covers the full parameter interval and full frequency range at 512 and 768 bits. It also replays the shifted-contour estimates at both ends of both brackets. A separate real-axis calculation checks the tight bracket by setting DEGREE=48 in d10_spectral_origin and calling run(512,n,10**12) for n=−398448207016 and n=−398448207015. Both methods use Arb. They give independent integral formulas for the origin signs and share the same analytic definition of the density.
