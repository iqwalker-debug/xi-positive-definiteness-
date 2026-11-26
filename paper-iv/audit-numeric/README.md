# Numerical certificates for the smallest eigenvalue and the dimension gap

Install `python-flint==0.8.0` and run `python paper-iv/audit-numeric/replay.py` from the repository root. The program rebuilds the strict matrix and gap bounds and checks the rounded profile constants in [certificates.json](certificates.json). All reported values in that file are decimal strings. Each computation uses the Arb backend with outward rounding and exits with an error on a failed check.

## The ten-observation matrix

The matrix contains two equal-time blocks with entries $F(8|i-j|)$, for indices $0\le i,j\le4$. The cross-time blocks have diagonals $(-3/50,1/2,1/2,0,-9/25)$ indexed by $|i-j|$. Here $F(t)$ is the cosine transform of the positive half-line theta density divided by its integral. Its $n$th summand at frequency $k\ge0$ is $e^{k/2-X}X(2X-3)$ with $X=\pi n^2 e^{2k}$.

`matrix.py` integrates the first eight theta terms of each cosine transform over twelve quarter-intervals covering $[0,3]$ at 224-bit precision. For each omitted region, $|\cos(tk)|\le1$. With $X_0=\pi n^2e^{2K}$, substituting $dk=dX/(2X)$ bounds the mass above $k=K$ by $(X_0^2+2X_0+2)e^{-X_0}$, since $e^{k/2}\le X$. This upper bound is at most $e^{-X_0/2}$ for $X_0\ge12$. For omitted indices $n\ge9$, consecutive exponents $\pi n^2/2$ differ by at least $19\pi/2$. Each of the eight retained indices has $X_0\ge\pi e^6$ beyond the integration range. The code allows a factor of two of slack on each majorant.

Every leading principal minor of the ten-by-ten matrix shifted by the lower endpoint is positive. Sylvester's criterion puts all ten eigenvalues above this rational. The determinant at the upper shift is strictly negative, so at least one eigenvalue lies below it. The two shifts are exactly $10^{-35}$ apart.

## The fixed-profile dimension gap

The comparison holds the normalized Xi profile $F$ fixed. It assumes the nonnegative, normalized nine-dimensional spectral law proved in [Paper I](../../Paper-I.pdf). Let $R$ be its radius and let $B$ be the length after projecting an independent uniform unit direction to eight dimensions. Then $B^2\sim\mathrm{Beta}(4,1/2)$. With $B=\cos\theta$, the angular density on $[0,\pi/2]$ is $2\cos^7(\theta)/\mathrm{Beta}(4,1/2)$. The conditional mean of $\Omega_8(5RB)$ is $\Omega_9(5R)$, where $\Omega_d$ is the uniform spherical characteristic function. Writing $x_-=\max(0,-x)$, the gap $H_8(5)-H_9(5)$ is the integral in $R$ of

$$2\left(\mathbb{E}_B[(\Omega_8(5RB))_-]-(\Omega_9(5R))_-\right).$$

This integrand lies in $[0,1]$ by Jensen's inequality and $|\Omega_d|\le1$. Directly integrating it avoids cancellation between two full supports of order one.

`dimension_gap.py` uses 180-bit arithmetic. It proves $\Omega_8(z)>0$ through $z=6.3$ using the cosine representation for $0\le z\le1$, then 5,300 subintervals and $|\Omega'_8|\le1$. Radii $R\le1.26$ therefore contribute zero. At $1.26\le R\le1.6$, angles $\theta\ge0.7$ have zero negative part. The program bounds the integrand on 6,144 radial cells and 3,072 angular cells. It evaluates a first-order Taylor expansion of each spherical kernel with $\Omega'_d(z)=-z\Omega_{d+2}(z)/d$ and $|\Omega''_d|\le1/d$. These bounds follow from the spherical Bessel recurrence and the second moment of a unit coordinate. A floating-point operation chooses a nearby Taylor center. Arb encloses the entire offset and the remainder for every cell.

For the nine-dimensional radius density, start with the even line density normalized by $Z=\xi(1/2)/2$. Apply the radial Fourier lift $-(2\pi r)^{-1}d/dr$ four times and multiply by the area factor $|S^8|r^8$. The resulting derivative combination, apart from the area, normalizer and powers of $2\pi$, is $r(r^3\Phi^{(4)}-6r^2\Phi^{(3)}+15r\Phi''-15\Phi')$. A recurrence constructs the theta derivative polynomials. On each radial cell the first summand is enclosed directly. For $x=\pi e^{2r}$ and $X=n^2x$, the code bounds the polynomial $P(X)/X^6$ on $0\le 1/X\le1/(4x)$. The omitted majorants for $n\ge2$ have ratio at most $(3/2)^{12}e^{-5x}$. The program checks that the resulting radius density is positive on every integrated cell.

For the remaining radii, $\Pr(R>1.6)\Pr(|U_1|>0.94)\le\Pr(|RU_1|>0.94\cdot1.6)$ by independence. The right side is a half-line theta tail divided by $Z/2$. With $x=\pi\exp(2\cdot0.94\cdot1.6)$, consecutive majorants $(n^4x^2+2n^2x+2)e^{-n^2x}$ have ratio at most $16e^{-3x}$. Integrating a lower bound for the absolute coordinate density on $[0.94,0.95]$ bounds the probability in the denominator. The radial mass beyond 1.6 is below $3.94\times10^{-19}$. As the conditional deficit lies in $[0,1]$, adding the interval from zero to this tail bound completes the enclosure.

## Fourth derivatives and the three-dimensional asymptotic

`profile_checks.py` expands $\xi(1/2+it)/\xi(1/2)$ through fourth order using Arb series at 192 bits. If $c_j$ is the coefficient of $t^j$, the spectral variance is $-2c_2$ and the Xi fourth derivative is $24c_4$. A Gaussian with variance $v$ has fourth derivative $3v^2$. For the three-dimensional large-separation constant $2p(0+)/\pi$, the same theta series gives $p(0+)=2\Phi(0)/Z$. The omitted terms $n\ge9$ are bounded by $2(\pi n^2)^2e^{-\pi n^2}$, whose successive ratio is at most $(10/9)^4e^{-19\pi}$. The program checks that each enclosure lies strictly inside the rounding interval of its reported decimal.
