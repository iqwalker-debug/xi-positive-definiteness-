"""Arb port of Sprint 02's radial sign certificate.
A successful run certifies the finite inequalities, conditional on the
analytic reductions and tail bounds in the Sprint 01 proof.
No floating-point sign decisions. Not an independently devised proof.
"""
from fractions import Fraction as F
from math import comb
from flint import arb, ctx
import flint, os, json

ctx.prec = int(os.environ.get("ARB_BITS", "192"))
PI = arb.pi()

def ball(q):
    q = F(q)
    return arb(q.numerator) / arb(q.denominator)

def symmetric(x):
    u = x.abs_upper()
    return (-u).union(u)

def require(condition, label):
    if not condition:
        raise ArithmeticError(label)

# Derivative recurrence: Q_(j+1)=(1/2-2X)Q_j+2XQ'_j.
P = [[F(0), F(-3), F(2)]]
for j in range(11):
    p = P[-1]
    q = [F(0)] * (len(p)+1)
    for k, v in enumerate(p):
        q[k] += (F(1,2)+2*k)*v
        q[k+1] -= 2*v
    P.append(q)
C = [sum(map(abs,p)) for p in P]
BP = [[ball(v) for v in p] for p in P]

def derivatives(a,b,orders):
    t = ball(a).union(ball(b))
    pre = (t/2).exp()
    X = PI*(2*t).exp()
    # Retain n=1..4; majorant for n>=5.
    X5 = 25*PI*(2*ball(a)).exp()
    out = {}
    for j in orders:
        val = arb(0)
        for n in range(1,5):
            x = n*n*X
            v = arb(0)
            for p in reversed(BP[j]):
                v = v*x+p
            val += v*(-x).exp()
        tail = 2*ball(C[j])*(ball(b)/2).exp()*X5**(j+2)*(-X5).exp()
        out[j] = pre*val+symmetric(tail)
    return out

def mid(a,b,j):
    c = (a+b)/2
    return derivatives(c,c,[j])[j]+symmetric(ball((b-a)/2)*derivatives(a,b,[j+1])[j+1])

def numerator(a,b):
    r = ball(a).union(ball(b))
    v = derivatives(a,b,[1,2,3,4])
    return r**3*v[4]-6*r**2*v[3]+15*r*v[2]-15*v[1]

def partition(a,b,near):
    todo=[(a,b,0)]
    count=0
    while todo:
        a,b,depth=todo.pop()
        v = mid(a,b,8) if near else numerator(a,b)
        if v > 0:
            count+=1
        else:
            require(depth<25, "subdivision limit: D9 inconclusive")
            c=(a+b)/2
            todo.extend([(a,c,depth+1),(c,b,depth+1)])
    return count

def main():
    require((ball(F(6,5))**26*(-11*PI).exp()) < ball(F(1,2)), "tail ratio")
    require(25*PI > 13, "tail monotonicity")
    require(PI*arb(2).exp() > 20, "D9 far-tail cutoff")
    for j in range(1,5):
        for l in range(len(P[j])):
            c=sum(P[j][k]*comb(k,l)*20**(k-l) for k in range(l,len(P[j])))
            require((-1)**j*c>0, "exact shifted polynomial sign")
    n1=partition(F(0),F(1,5),True)
    n2=partition(F(1,5),F(1),False)
    print("D9 positivity PASS",n1,n2,flush=True)
    N=3200
    L=None
    M=arb(0)
    for k in range(N):
        v=mid(F(k,N),F(k+1,N),10)
        u=v.abs_upper()
        if u>M: M=u
        if k<N//20:
            lo=v.lower()
            if L is None or lo<L: L=lo
    require(L is not None and L>0, "D10 near lower bound")
    u0=derivatives(F(0),F(0),[8])[8]/105
    near=-L*ball(F(1,20))/1890
    middle=arb(0)
    N=1600
    for k in range(N//20,N):
        a,b=F(k,N),F(k+1,N)
        c=(a+b)/2
        uc=numerator(c,c)/ball(c)**7
        err=M*ball(b*(b-a)/2)/945
        middle+=(u0-uc+symmetric(err))*ball(1/a-1/b)
    J=near+middle+u0.upper()
    require(J<0, "D10 obstruction not certified")
    result={"python_flint":flint.__version__,"bits":ctx.prec,"D9_near_cells":n1,
            "D9_middle_cells":n2,"D10_J_enclosure":str(J),
            "D10_upper_bound":str(J.upper()),"status":"PASS",
            "scope":"finite sign inequalities and exact tail polynomial checks; analytic proof separately required"}
    print(json.dumps(result,indent=2),flush=True)
    with open("arb-results.json","w") as f: json.dump(result,f,indent=2)

if __name__=="__main__": main()
