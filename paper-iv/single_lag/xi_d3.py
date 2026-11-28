"""Enclose the three-dimensional single-lag envelope of the Xi spatial covariance."""
import json
import flint
from flint import acb, arb, ctx

def check(value, message):
    if not value:
        raise ArithmeticError(message)

def enclose(bits):
    ctx.prec = bits
    pi = arb.pi()
    def theta(k):
        result = acb(0)
        for n in range(1, 9):
            x = pi*n*n*(2*k).exp()
            result += (k/2-x).exp()*x*(2*x-3)
        return result
    # phi is a positive sum. For x0>=16 in the omitted ranges, substituting
    # x=pi*n²exp(2k) bounds each omitted integral by 2exp(-x0/2).
    q = (-pi*arb(4).exp()/2).exp()
    r = (-9*pi/2).exp()
    tail = (2*q/(1-q) + 2*r**9/(1-r)).upper()
    opts = dict(rel_tol=arb(2)**-120, abs_tol=arb(2)**-120)
    normal = acb.integral(lambda z, analytic:theta(z), 0, 2, **opts).real + arb(0).union(tail)
    results = []
    for a in (2,4,5,8,10):
        # Integration by parts gives H3 = E_p[sgn(sin(ak))*cos(ak)].
        bounds=[arb(0)]
        for j in range(1,2*a+1):
            x=pi*j/a
            if x<2:
                bounds.append(x)
            elif not x>2:
                raise ArithmeticError("Unresolved integration boundary")
        bounds.append(arb(2))
        numerator = acb(0)
        for j,(left,right) in enumerate(zip(bounds,bounds[1:])):
            numerator+=acb.integral(lambda z, analytic:(-1)**j*theta(z)*(a*z).cos(),left,right,**opts)
        h=(numerator.real+arb(0,tail))/normal
        check(numerator.imag.contains(0) and h.rad() < arb(10)**-27, "Quadrature failed")
        results.append(dict(a=a,enclosure=h.str(36)))
    return dict(bits=bits,rows=results,total_mass_tail=tail.str(12))

if __name__=='__main__':
    print(json.dumps(dict(python_flint=flint.__version__,results=[enclose(192),enclose(256)]),indent=2))
