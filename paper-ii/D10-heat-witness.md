# A single finite D10 witness over a heat interval

For every real parameter $0\le s\le 1$, the spacing-7 weighted grid from Paper I has strictly negative Gram form for the normalized heat-deformed Xi profile. The same points and weights work throughout the interval.

Write $c_j$ for the ordered-pair histogram coefficients of that grid, $N$ for its positive normalization, $S=\sum c_j/N$, and
\[
q(r)=\sum_j (c_j/N)\cos(7\sqrt j\,r), \qquad
I(s)=\int_0^\infty e^{sr^2}\Phi(r)q(r)\,dr .
\]
The verifier proves $I(s)<-1/1000$ uniformly. The normalized Gram form is $I(s)/\int_0^\infty e^{sr^2}\Phi(r)\,dr$, with positive denominator. The bound $-1/1000$ applies to the unnormalized half-line integral. Dimension restriction and Paper II's D9 upper endpoint below 1 exclude larger parameters in D10. Thus this route to the coexistence cutoff uses the finite witness directly. It requires no sphere disintegration or all-dimensional downward closure.

## Enclosing the infinite integral

On $0\le r\le 2$ use 128 panels of half-width $h=1/128$ and 16-point Gauss–Legendre quadrature on each. Around each midpoint take a complex disk of radius $D=1/8$. Let $X_n(z)=\pi n^2e^{2z}$, $U=\pi e^{2(2+D)}$. Throughout the disks, $|X_n|\le U n^2$ and $\Re X_n\ge\pi e^{-2D}\cos(2D)n^2>2n^2$. The theta series converges normally there, and
\[
|\Phi(z)|\le 2e^{(2+D)/2} U(2U+3)/(e-1).
\]
Indeed $n^4\le2e^{n^2}$ and $\sum_{n\ge1}e^{-n^2}\le1/(e-1)$. Multiply this bound by $S e^{7\sqrt{810}D}e^{(2+D)^2}$ to bound the full integrand by $M$ on every disk, uniformly in $s$.

Cauchy's coefficient bound gives a maximum Taylor remainder $M(h/D)^{32}/(1-h/D)$ beyond degree 31. The quadrature rule is exact through degree 31 and has positive weights summing to the panel length. Applying the same remainder bound to both the integral and the rule gives total error at most $4M(h/D)^{32}/(1-h/D)$ on the length-two interval. The implementation obtains enclosed nodes and weights from Arb. [NIST DLMF, §3.5(v)](https://dlmf.nist.gov/3.5#v)

For $r\ge2$, use $2X^2\le16 e^{X/2}$ for $X\ge0$. Split the remaining $X_n/2$ into quarters. The bound $e^{2r}\ge1+2r+2r^2$ gives $X_n/4\ge r^2+3r/2$. Also $\pi e^4/4>41$ gives $X_n/4\ge40+n$. Therefore $e^{sr^2}|\Phi(r)q(r)|\le 16S e^{-40-r}/(e-1)$. Integration gives the tail bound $16S e^{-42}/(e-1)$.

## Covering the full parameter interval

At each real quadrature node include theta summands $1\le n<13$. Their omitted absolute sum is at most $16 e\,e^{-13^2-13}/(1-e^{-1})$, since $X_n/2\ge n^2+n$ for $n\ge13$. The code encloses the contributions to all coefficients of the degree-48 Taylor polynomial in $s$ for the quadrature sum. Its uniform Taylor error is at most $e^4 4^{49}/49!$ times the sum of absolute weighted sample values before multiplying by the heat factor. On each of 256 closed, adjoining parameter intervals, interval Horner evaluation plus all three errors has upper endpoint below $-1/1000$. The runs at 192 and 256 bits use the same mathematical argument.

## Three fixed bounds imply negativity throughout the interval

Write $w=\Phi q$ and define the signed half-line moments
$m_j=\int_0^\infty w(r)r^{2j}/j!\,dr$. Arb encloses the moments through degree 48 and checks three rational bounds,
\[
m_0\le -3/2000,\qquad m_1\le -1,\qquad
\sum_{j=2}^{48}\max(m_j,0)\le 3/4 .
\]
The quadrature bound above applies to each moment because $|z|^{2j}/j!\le e^{|z|^2}$ on each complex disk. On the real tail, $r^{2j}/j!\le e^{r^2}$. The script adds both errors to each moment upper bound before taking positive parts.

Lean bounds the remaining exponential series under the integral. For $x\ge0$, its terms of order $j\ge49$ have sum at most $3^{-49}e^{3x}$. For the concrete grid $|q|\le10^{10}$, and the theta series obeys $e^{3r^2}\Phi(r)\le32 e^{-r}$ for $r>0$. Thus the integrated absolute remainder is at most $32\cdot10^{10}/3^{49}<10^{-6}$. The script also checks a remainder bound by its original compact-interval and tail estimates.

For $0\le s\le1$ and $j\ge2$, $s^jm_j\le s\max(m_j,0)$. Integrating the truncated series and applying the three fixed bounds gives
\[
I(s)\le-\frac{1499}{10^6}-\frac{s}{4}.
\]
This is a bound on the unnormalized half-line integral. The uniform sign is a Lean conclusion. The three moment bounds are external numerical inputs. [Lean proof](lean/HeatMomentCertificate.lean)

## Replay

From the Paper II directory with its pinned Python dependencies installed, run:

```sh
python certify_d10_heat.py
python certify_sharp.py --d9-witness
```

The second command checks $Q_4(x;1/16)>0$ on the full half-line at 512 and 768 bits. It checks the value directly on the first interval and uses the exact rational parameter throughout. The proof of the D9 criterion in the manuscript turns this into a positive D9 witness. Since $0.22/4 <1/16$, that parameter also lies in the real-zero range.
