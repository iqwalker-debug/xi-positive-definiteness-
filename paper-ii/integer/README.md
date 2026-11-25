# Independent verification of Walker's Paper II

The independent verifier reads the thirteen rational brackets from the first precision block of `../heat-upper-bounds.json`. It computes its own coefficient enclosures, bracket signs and regional inequalities using Python's standard library. From this directory run `python upper.py` and `python sharp.py` with assertions enabled. Each script exits on the first uncertified inequality. Printed decimals are for inspection. The two implementations share the analytic reduction.

## Integer balls and elementary constants

An interval [L,U] represents [L/S,U/S] with S=2^640 or 2^1400. Four-endpoint products or equivalent sign-specific endpoint products round downward and upward. Machin's identity pi = 16 arctan(1/5)-4 arctan(1/239) and alternating rational partial sums bound pi. To calculate exp(-x) range-reduce by a power of two until its argument has absolute value less than one, bound it by consecutive alternating exponential partial sums, then repeatedly square.

## Different Taylor coefficient method

Put X=pi*n^2. The nth theta summand is
  2 X^2 exp(-X) exp((9/2)r-X(exp(2r)-1)) - 3 X exp(-X) exp((5/2)r-X(exp(2r)-1)).
For h=br-X(exp(2r)-1) and u=exp(h), use j*u_j=sum_{k=1}^j k*h_k*u_{j-k} from u'=h'u. The coefficient of r^{2j} is the coefficient a_j in H(x)=Phi(sqrt(x)). On |r|=1/8, |X exp(2r)|<6n^2 and Re(X exp(2r))>2n^2; these use pi>3, pi<4, exp(-1/4)>=3/4, exp(1/4)<=4/3 and cos(1/4)>=31/32. The prefactor exp(r/2) has modulus <2, so each summand is bounded by 180 n^4 exp(-2 n^2). For n>=N>=14, n^4<=exp(n^2/2). Consecutive exp(-3n^2/2) decrease by more than a factor of two. Cauchy on |r|=1/8 therefore bounds each omitted a_j by 360*8^{2j}*2^{-3N^2/2}, using e>2. Use N=14 for the roots, N=30 for sharpness.

## Upper bounds

Retain coefficients j=0,...,13. The proposed brackets have opposite signs, and each upper endpoint lies left of the preceding lower endpoint. P_0=a_0>0 (independently follows from positive theta density, also enclosed). From the definitions, P'_m=-P_{m-1}. Inductively P_{m-1}>0 to the left of its smallest root, so P_m is strictly decreasing there. Together with its two bracket signs this proves its smallest real root and excludes a sign return before the preceding root. For m=1 use P_0>0. With subspace restriction and Q_m(0)=m!P_m this proves the necessary upper bounds; no global root bound is needed in this verifier. Each bracket is bisected 30 times by directed sign decisions, to width 2e-12/2^30.

## Sharpness

For |x|<=3/5 choose |r|=sqrt(|x|)<31/40. Then |X exp(2r)|<32 n^2, using e^2<8 and pi<4. The real part exceeds n^2/1000: pi>3, exp(-2|r|)>1/8, cos(2 Im r)>=cos(31/20)>1/100 since pi/2-31/20>1/50 and sin(v)>=v/2 in [0,1]. The outer |exp(r/2)|<2. Set q=1000/1001. Since exp(-n^2/1000)<=q^n and sum n^4 q^n<=24/(1-q)^5, the supremum |H(x)| is bounded by M=2^67. (The numerical inequality 2*32*67*24*1001^5<M is checked.) Use the Cauchy coefficient estimate |a_k|<=M(3/5)^(-k). Beyond degree 120 and on |x|<=d=1/4 the jth derivative tail is bounded by 2 M d^{-j}121^j(d/(3/5))^121, since the successor ratio for the k^j majorant is <1/2, checked for every j used.

Certify dQ_m/dx>0 on [0,1/16] and Q_m>0 on [1/16,1/4] over the entire input lambda bracket by adaptive bisection. Only at the exact root do we invoke Q_m(0)=0 to deduce positivity near zero. For x>=1/4 implement the recurrence from Paper II using rational sparse polynomials in (r,X,lambda). Expand r=1/2+z and X=(8539/1000)(1+2z+2z^2)+u by binomial/multinomial identities. Every nonzero coefficient polynomial in lambda, including the constant in (z,u), is strictly positive over the bracket. Check pi*sum_{j<=10}1/j!>8539/1000 for u>=0. This proves the tail summand-by-summand. The default loop covers every odd dimension from 5 through 27.
