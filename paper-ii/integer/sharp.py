"""Referee reimplementation of the global three-region sign certificate.
Run with Python's standard library and with assertions enabled.
"""
if not __debug__:
    raise SystemExit("Verification requires Python assertions. Remove -O or PYTHONOPTIMIZE.")

import argparse
from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path
S = 1 << 1400

def ceil_ratio(n,d): return -((-n)//d)
def rat(x):
    x=F(x)*S
    return (x.numerator//x.denominator, ceil_ratio(x.numerator,x.denominator))
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def neg(a): return (-a[1],-a[0])
def mul(a,b):
    if a[0]>=0 and b[0]>=0: return ((a[0]*b[0])>>1400,-((-a[1]*b[1])>>1400))
    if a[1]<=0 and b[1]<=0: return ((a[1]*b[1])>>1400,-((-a[0]*b[0])>>1400))
    if a[0]>=0 and b[1]<=0: return ((a[1]*b[0])>>1400,-((-a[0]*b[1])>>1400))
    if a[1]<=0 and b[0]>=0: return ((a[0]*b[1])>>1400,-((-a[1]*b[0])>>1400))
    vals=[u*v for u in a for v in b]
    return (min(vals)>>1400,-((-max(vals))>>1400))
def fac(a,x): return mul(a,rat(x))
def arctan(a):
    n=100
    p=sum(F((-1)**j,(2*j+1)*a**(2*j+1)) for j in range(n))
    return (rat(p)[0],rat(p+F(1,(2*n+1)*a**(2*n+1)))[1])
pi=add(fac(arctan(5),16),fac(arctan(239),-4))
def exp_neg(x):
    # t = x/4096 is nonnegative and no larger than one.
    t=fac(x,F(1,4096))
    assert 0<t[0]<=t[1]<S
    term=z=rat(1)
    for j in range(1,180):
        term=fac(mul(term,t),F(-1,j))
        if j==179: even=z
        z=add(z,term)
    a=(z[0],even[1])
    for i in range(12): a=mul(a,a)
    return a
def exp_composite(x,b,N):
    # [r^j] exp(br - x (exp(2r)-1))
    h=[rat(0)]+[fac(x,-F(2**j,factorial(j-1))) for j in range(1,N+1)]
    h[1]=add(h[1],rat(b))
    u=[rat(1)]
    for j in range(1,N+1):
        s=rat(0)
        for k in range(1,j+1): s=add(s,mul(h[k],u[j-k]))
        u.append(fac(s,F(1,j)))
    return u
from math import comb
from functools import lru_cache
from collections import defaultdict
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--max-m', type=int, default=13, choices=range(2, 14))
max_m = parser.parse_args().max_m
K=120
ca=[rat(0) for j in range(K+1)]
for n in range(1,30):
    x=fac(pi,n*n)
    ex=exp_neg(x)
    u=exp_composite(x,F(9,2),2*K)
    v=exp_composite(x,F(5,2),2*K)
    for j in range(K+1):
        val=mul(mul(x,ex),add(fac(mul(x,u[2*j]),2),fac(v[2*j],-3)))
        ca[j]=add(ca[j],val)
for j in range(K+1):
    err=rat(F(360*8**(2*j),2**1350))[1]
    ca[j]=add(ca[j],(-err,err))
print('enclosed all coefficients',flush=True)
D=F(1,4); R=F(3,5)
M=2**67
assert 2*32*67*24*1001**5<M
source = Path(__file__).resolve().parent.parent / "heat-upper-bounds.json"
rows = json.loads(source.read_text())[0]["results"]
assert [row["m"] for row in rows] == list(range(1, 14))
all_dp=[]
for j in range(max_m+2):
    dp=[fac(ca[k],factorial(k)//factorial(k-j)) for k in range(j,K+1)]
    assert (F(K+2,K+1)**j)*D/R<F(1,2)
    err=rat(2*M*D**(-j)*(K+1)**j*(D/R)**(K+1))[1]
    all_dp.append((list(reversed(dp)),err))
def horner(co,x):
    s=rat(0)
    for c in co: s=add(mul(s,x),c)
    return s
@lru_cache(None)
def H(k,l,r):
    p,e=all_dp[k]
    return add(horner(p,(l,r)),(-e,e))
def fixpow(v,n):
    a=rat(1)
    for _ in range(n): a=mul(a,v)
    return a
w={(0,2,0):F(2),(0,1,0):F(-3)}
for m in range(1,max_m+1):
    v=defaultdict(F)
    for (i,j,k),b in w.items():
        v[i+1,j+1,k]+=2*b
        v[i+1,j,k]-=(F(1,2)+2*j)*b
        v[i,j,k]+=(2*(m-1)-i)*b
        v[i+2,j,k+1]-=2*b
    w={p:c for p,c in v.items() if c}
    if m==1:continue
    row=rows[m-1]; L=(rat(row['lower'])[0],rat(row['upper'])[1])
    cs=[fac(fixpow(L,m-k),(-1)**m*comb(m,k)) for k in range(m+1)]
    def cover(l,r,shift,depth=0):
        sl,sr=rat(l)[0],rat(r)[1]
        s=rat(0)
        for k,cc in enumerate(cs): s=add(s,mul(H(k+shift,sl,sr),cc))
        if s[0]>0:return 1
        assert depth<20,(m,l,r,s[0]/S,s[1]/S)
        mid=(l+r)/2
        return cover(l,mid,shift,depth+1)+cover(mid,r,shift,depth+1)
    A=cover(F(0),F(1,16),1); B=cover(F(1,16),F(1,4),0)
    # Expand after X=c(1+2z+2z^2)+u, r=1/2+z directly by binomial/multinomial formula.
    c=F(8539,1000); Z=defaultdict(F)
    exp_one_lower=sum(F(1,factorial(j)) for j in range(11))
    assert mul(pi,rat(exp_one_lower))[0]>rat(c)[1]
    for (i,j,k),b in w.items():
        for ir in range(i+1):
            for ju in range(j+1):
                t=j-ju
                mult=b*comb(i,ir)*F(1,2)**(i-ir)*comb(j,ju)*c**t
                for a in range(t+1):
                    for b2 in range(t-a+1):
                        Z[ir+a+2*b2,ju,k]+=mult*comb(t,a)*comb(t-a,b2)*2**(a+b2)
    gr=defaultdict(lambda:defaultdict(F))
    for (z,u,k),b in Z.items():
        if b: gr[z,u][k]=b
    assert (0,0) in gr
    for key,poly in gr.items():
        cc=[rat(poly.get(j,0)) for j in range(max(poly),-1,-1)]
        assert horner(cc,L)[0]>0,(m,key)
    print('d',2*m+1,'A',A,'B',B,'tail',len(gr),flush=True)
