"""Sharp joint covariance region for a fixed Xi equal-time law, a=8, any chosen tau != 0.
Requires Python 3.10+, numpy and scipy. Writes JSON/CSV beside this file.
A deterministic split Gauss–Legendre rule uses all analytic sign switches.
"""
from pathlib import Path
import csv
import json
import numpy as np
import scipy
from scipy.integrate import quad
from scipy.linalg import toeplitz

A=8
KMAX=2
ROOT=Path(__file__).parent
def raw(k):
    k=np.asarray(k)
    z=np.pi*np.arange(1,5,dtype=float).reshape((-1,)+(1,)*k.ndim)**2*np.exp(2*k)
    return np.sum(np.exp(k/2-z)*z*(2*z-3),axis=0)

def breaks(b,c):
    if abs(c)<1e-15:
        roots=[0]
    else:
        roots=[v.real for v in np.roots([2*c,b,-c]) if abs(v.imag)<1e-13 and abs(v.real)<=1+1e-14]
    bounds={0,KMAX}
    for v in roots:
        phi=np.arccos(np.clip(v,-1,1))
        for m in range(-1,5):
            for sign in (1,-1):
                k=(sign*phi+2*np.pi*m)/A
                if 0<k<KMAX:
                    bounds.add(float(k))
    return np.array(sorted(bounds))

def legendre(fun, bounds, order):
    t, w=np.polynomial.legendre.leggauss(order)
    lo,hi=bounds[:-1],bounds[1:]
    x=(lo+hi)[:,None]/2+(hi-lo)[:,None]*t/2
    weights=(hi-lo)[:,None]*w/2
    return float(np.sum(fun(x)*weights))

def projection(b,c,order):
    ranges=breaks(b,c)
    norm=legendre(raw,np.array([0,KMAX]),order)
    def normal(k):
        return np.sign(b*np.cos(A*k)+c*np.cos(2*A*k))
    x=legendre(lambda k:raw(k)*normal(k)*np.cos(A*k),ranges,order)/norm
    y=legendre(lambda k:raw(k)*normal(k)*np.cos(2*A*k),ranges,order)/norm
    return x,y,b*x+c*y

def independent_quadrature(b,c):
    fun=lambda k:float(raw(k))*abs(b*np.cos(A*k)+c*np.cos(2*A*k))
    val=quad(fun,0,KMAX,points=breaks(b,c)[1:-1],epsabs=2e-15,epsrel=2e-14)[0]
    norm=quad(raw,0,KMAX,epsabs=2e-15,epsrel=2e-14)[0]
    return val/norm

def main():
    angles=np.arange(360)*np.pi/180
    out=[]
    for deg,t in enumerate(angles):
        b,c=np.cos(t),np.sin(t)
        x,y,h=projection(b,c,48)
        out.append([deg,b,c,x,y,h])
    with (ROOT/'joint-boundary.csv').open('w') as f:
        w=csv.writer(f); w.writerow(['normal_degrees','u1','u2','boundary_C8','boundary_C16','support']);w.writerows(out)
    zn=legendre(raw,np.array([0,KMAX]),64)
    moments=np.array([legendre(lambda k:raw(k)*np.cos(j*A*k),np.array([0,KMAX]),64)/zn for j in range(5)])
    G=np.array([[(1+moments[2])/2,(moments[1]+moments[3])/2],[(moments[1]+moments[3])/2,(1+moments[4])/2]])
    witness=np.array([.5,.5]); K=toeplitz(moments); J=toeplitz([-.06,.5,.5,0,-.36])
    refs={}
    for b,c in [(1,0),(0,1),(1,1),(1,-1)]:
        x,y,h=projection(b,c,64)
        refs[f'{b},{c}']={'h':h,'attaining_pair':[x,y],'scipy_quad_h':independent_quadrature(b,c),'local_reflected_Cauchy_bound':float(np.sqrt(np.array([b,c])@G@[b,c]))}
    obj={'python_numerics':{'numpy':np.__version__,'scipy':scipy.__version__},'a':A,'max_k':KMAX,'theta_terms':4,'raw_density_integral':zn,'equal_time_at_lags_0_a_2a_3a_4a':moments.tolist(),'supports':refs,'witness':witness.tolist(),'violation_for_u_1_1':float(witness.sum()-refs['1,1']['h']),'G_reflected_local_spatial_gram':G.tolist(),'reflected_local_schur_quadratic':float(witness@np.linalg.solve(G,witness)),'two_time_five_site_cross_row':J[0].tolist(),'eigmin_KplusJ':float(np.linalg.eigvalsh(K+J)[0]),'eigmin_KminusJ':float(np.linalg.eigvalsh(K-J)[0])}
    (ROOT/'joint-results.json').write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps(obj,indent=2))
if __name__=='__main__':main()
