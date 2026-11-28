"""Standalone certificate, Python 3.12 and python-flint 0.8.0.

For F(t)=Xi(t)/Xi(0), compute H(a)=E_mu|cos(aK)| and local Gram upper
bound B(a)=sqrt((1+F(2a))/2). See the analytic witnesses below. Runtime
validation uses explicit exceptions, including when Python runs with -O.
"""
from functools import lru_cache
import json
import flint
from flint import acb, arb, ctx

def require(claim, message):
    if not claim:
        raise ArithmeticError(message)

def outputs(bits):
    ctx.prec = bits
    pi = arb.pi()
    @lru_cache(None)
    def xi(t):
        s = acb(arb(1)/2, t)
        z = s*(s-1)/2 * (-s/2*pi.log()).exp() * (s/2).gamma() * s.zeta()
        require(z.imag.contains(0), "Critical Xi must be real")
        return z.real
    center = xi(0)
    require(center > arb(1)/4, "Central normalization bound")
    def profile(t):
        return xi(t)/center
    # Euler summation gives |zeta(1/2+it)| <= 1+2|1/2+it| <= 2+2t.
    # Rotate Euler's Gamma integral by pi/4, obtaining
    # |Gamma(1/4+it/2)| <= Gamma(1/4)*2^(1/8)*exp(-pi*t/8).
    # Splitting that Gamma integral at 1 gives Gamma(1/4) < 4+1 = 5.
    # With pi>3, Xi(0)>1/4 and |s(s-1)|=t^2+1/4, this yields
    # |F(t)| <= 40*(1+t)^3*exp(-3t/8), t >= 0.
    # The remaining geometric ratio starting at n=N+1 is <=
    # ((N+2)/(N+1))^3 exp(-3a/4); drop the denominator 4n^2-1.
    rows=[]
    N=64
    for a in [2,4,5,8,10]:
        first=N+1
        ratio=(arb(first+1)/first)**3 * (-arb(3*a)/4).exp()
        require(ratio < arb(1)/2, "Harmonic tail ratio")
        radius=160*(1+2*a*first)**3 * (-arb(3*a*first)/4).exp()
        h=2/pi
        for n in range(1,N+1):
            h+=(4/pi) * ((-1)**(n+1)) * profile(2*n*a)/(4*n*n-1)
        h+=arb(0,radius.upper())
        b=((1+profile(2*a))/2).sqrt()
        require(0 < h and h < b and b < 1, "Nontrivial strict gap")
        rows.append((a,h,b,b-h,radius))
    return rows

def direct_five(bits):
    """Independent theta-space integral, without zeta, gamma or Fourier coefficients."""
    ctx.prec=bits
    pi=arb.pi()
    def phi(z):
        e=(2*z).exp()
        p=acb(0)
        for n in range(1,9):
            x=pi*n*n*e
            p+=(z/2-x).exp()*x*(2*x-3)
        return p
    # On r>=0 all terms are positive. Substituting x=pi*n^2*exp(2r)
    # shows their mass from a point with lower x>=16 is bounded by
    # integral_x^inf u^(5/4)*e^(-u)du <= 2 exp(-x/2).
    # The last inequality uses u^(5/4)<=exp(u/2) for u>=16.
    # For r>=2, n^2>=n gives a geometric majorant with A=pi*exp(4).
    A=pi*arb(4).exp()
    q=(-A/2).exp()
    radial=2*q/(1-q)
    # For n>=9, n^2>=9n and start from r=0.
    q=(-9*pi/2).exp()
    indices=2*q**9/(1-q)
    epsilon=(radial+indices).upper()
    # All integrands below are entire on each cell. Resolve zeros explicitly.
    boundaries=[arb(0)]+[pi*(2*k+1)/10 for k in range(3)]+[arb(2)]
    args=dict(rel_tol=arb(2)**-125,abs_tol=arb(2)**-125)
    numerator=arb(0)
    denominator=arb(0)
    for k,(l,r) in enumerate(zip(boundaries,boundaries[1:])):
        num=acb.integral(lambda z, analytic: (-1)**k*phi(z)*(5*z).cos(),l,r,**args)
        den=acb.integral(lambda z, analytic: phi(z),l,r,**args)
        require(num.imag.contains(0) and den.imag.contains(0), "Real theta integrals")
        numerator+=num.real
        denominator+=den.real
    # Omitted numerator/denominator masses lie in [0,epsilon].
    omitted=arb(0).union(epsilon)
    u=(numerator+omitted)/(denominator+omitted)
    require(u.is_finite() and u.rad() < arb(10)**-27,"Theta precision")
    return u,epsilon

def main():
    raw=[]
    for bits in [192,256]:
        rows=outputs(bits)
        u,tail=direct_five(bits)
        require(u.overlaps(rows[2][1]),"Independent theta quadrature disagrees")
        a,h,b,_,_=rows[2]
        r=2*b*b-1
        c=arb(7)/10
        determinant=(1-r)*(1+r-2*c*c)
        require(-1<r and r<1 and h<c and determinant>0, "Exact local/global witness")
        raw.append(dict(bits=bits, counterexample=dict(a=a, L=2*a, c="7/10",
            F10=r.str(38), local_gram_determinant=determinant.str(38),
            excess_over_global=(c-h).str(38)), rows=[dict(a=a,L=2*a,envelope=h.str(38),
            gram_bound=b.str(38),gap=g.str(38),fourier_tail_bound=e.str(12))
            for a,h,b,g,e in rows], independent_a5=u.str(38),theta_tail=tail.str(12)))
    print(json.dumps(dict(python_flint=flint.__version__,FLINT=flint.__FLINT_VERSION__,
        harmonics=64,results=raw),indent=2))

if __name__=="__main__":
    main()
