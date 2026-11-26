"""Outward-rounded joint-gate proof (python-flint 0.9.0).
The bounds are Riemann sums, independent of the root-based floating-point rule.
A separate Sylvester test checks positive definiteness on 5 sites x 2 times.
"""
from pathlib import Path
import json
import flint
from flint import arb, acb, arb_mat
flint.ctx.prec=128
B=arb
A=8
N=8192
assert N & (N-1)==0
PI=B.pi()
tail=B('1e-15')
def enclose(factor):
    return B(0, tail*factor)
def critical_xi(r):
    z=acb(B(1)/2,B(r))
    return z*(z-1)/2*(-z*PI.log()/2).exp()*(z/2).gamma()*z.zeta()
def main():
    sums=[B(0) for _ in range(4)]
    for j in range(N):
        # Uniform partition of 0 <= k <= 2, cells with radius 1/N.
        k=B(B(2*j+1)/N, B(1)/N)
        z0=PI*(2*k).exp()
        raw=B(0)
        for i in range(1,5):
            x=z0*i*i
            raw+=(k/2-x).exp()*x*(2*x-3)
        c1=(A*k).cos()
        c2=(2*A*k).cos()
        for i, f in enumerate((1,abs(c1),abs(c2),abs(c1+c2))):
            sums[i]+=raw*f
    totals=[s*2/N+enclose(factor) for s,factor in zip(sums,(1,1,1,2))]
    h1,h2,hs=[x/totals[0] for x in totals[1:]]
    assert h1>B('0.63') and h2>B('0.63') and hs<B('0.94')
    # K from the cosine transform of the normalized Xi spectral measure.
    X0=critical_xi(0)
    R=[B(1)]+[(critical_xi(i*A)/X0).real for i in range(1,5)]
    J=[B(-3)/50,B(1)/2,B(1)/2,B(0),B(-9)/25]
    minors={}
    for sign in [1,-1]:
        row=[i+sign*j for i,j in zip(R,J)]
        row[0]-=B(1)/50
        md=[]
        for n in range(1,6):
            M=arb_mat([[row[abs(i-j)] for j in range(n)]for i in range(n)])
            determinant=M.det()
            assert determinant>0
            md.append(str(determinant))
        minors[str(sign)]=md
    obj={'engine':'python-flint '+flint.__version__,'precision_bits':flint.ctx.prec,'panels':N,'integration_upper_limit':2,'theta_terms':4,'omitted_raw_mass_upper':'1e-15','total_raw_mass_ball':str(totals[0]),'axis_8_support_ball':str(h1),'axis_16_support_ball':str(h2),'sum_support_ball':str(hs),'certified_simple_bounds':['h(1,0)>0.63','h(0,1)>0.63','h(1,1)<0.94','min eigenvalue of local 10x10 block >1/50'],'leading_minors_of_K_plus_or_minus_J_minus_I_over_50':minors}
    (Path(__file__).parent/'joint-certificate.json').write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps(obj,indent=2))
if __name__=='__main__':main()
