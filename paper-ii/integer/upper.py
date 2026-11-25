if not __debug__:
    raise SystemExit("Verification requires Python assertions. Remove -O or PYTHONOPTIMIZE.")

from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path
S = 1 << 640

def ceil_ratio(n,d): return -((-n)//d)
def rat(x):
    x=F(x)*S
    return (x.numerator//x.denominator, ceil_ratio(x.numerator,x.denominator))
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def neg(a): return (-a[1],-a[0])
def mul(a,b):
    vals=[u*v for u in a for v in b]
    return (min(vals)//S,ceil_ratio(max(vals),S))
def fac(a,x): return mul(a,rat(x))
def arctan(a):
    n=100
    p=sum(F((-1)**j,(2*j+1)*a**(2*j+1)) for j in range(n))
    return (rat(p)[0],rat(p+F(1,(2*n+1)*a**(2*n+1)))[1])
pi=add(fac(arctan(5),16),fac(arctan(239),-4))
def exp_neg(x):
    # t = x/1024 is nonnegative and no larger than one.
    t=fac(x,F(1,1024))
    assert 0<t[0]<=t[1]<S
    term=z=rat(1)
    for j in range(1,94):
        term=fac(mul(term,t),F(-1,j))
        if j==93: even=z
        z=add(z,term)
    a=(z[0],even[1])
    for i in range(10): a=mul(a,a)
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
a=[rat(0) for j in range(14)]
for n in range(1,14):
    x=fac(pi,n*n)
    ex=exp_neg(x)
    u=exp_composite(x,F(9,2),26)
    v=exp_composite(x,F(5,2),26)
    for j in range(14):
        val=mul(mul(x,ex),add(fac(mul(x,u[2*j]),2),fac(v[2*j],-3)))
        a[j]=add(a[j],val)
for j in range(14):
    err=rat(F(360*8**(2*j),2**294))[1]
    a[j]=add(a[j],(-err,err))
assert a[0][0]>0
def P(m,q):
    p=rat(0)
    for j in range(m+1):
        p=add(mul(p,rat(q)),fac(a[j],F((-1)**m,factorial(m-j))))
    return p
source = Path(__file__).resolve().parent.parent / "heat-upper-bounds.json"
rows = json.loads(source.read_text())[0]["results"]
assert [row["m"] for row in rows] == list(range(1, 14))
print('d  published lo sign floor, hi sign upper; improved root bracket (units of 10^-22; lower rounded down, upper rounded up)')
for row in rows:
    m=row['m']
    lo,hi=F(row['lower']),F(row['upper'])
    if m>1: assert hi<prev
    prev=lo
    lval,rval=P(m,lo),P(m,hi)
    assert lval[0]>0 and rval[1]<0
    for k in range(30):
        mid=(lo+hi)/2
        p=P(m,mid)
        if p[0]>0: lo=mid
        elif p[1]<0: hi=mid
        else: raise ValueError('Uncertain sign')
    def dec(x): return f'{x.numerator*10**22//x.denominator}'
    print(2*m+1,'%.3e'%(lval[0]/S),'%.3e'%(rval[1]/S),dec(lo), str(-((-hi.numerator*10**22)//hi.denominator)))
