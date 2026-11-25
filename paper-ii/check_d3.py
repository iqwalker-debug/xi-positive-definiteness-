"""Rerun with python-flint 0.9.0, Python assertions enabled."""
from fractions import Fraction as F
import json
from flint import arb, ctx

def ball(x):
    x = F(x)
    return arb(x.numerator) / x.denominator

def run(bits):
    ctx.prec = bits
    pi = arb.pi()
    polys = [[F(0), F(-3), F(2)]]
    for _ in range(4):
        old = polys[-1]
        polys.append([(F(1,2)+2*j)*(old[j] if j < len(old) else 0)
                      - (2*old[j-1] if j else 0) for j in range(len(old)+1)])
    coeffs = [[ball(c) for c in row] for row in polys]
    # Uniform derivative tail, on [0,1]. For n >= 10, X >= 3*n^2.
    # Each |P_j(X)| <= C X^6. Since X^6 exp(-X/2) decreases for
    # X >= 300, use exp(-X/2) to sum the remaining terms geometrically.
    C = max(sum(map(abs, p)) for p in polys)
    bound = (ball(C)*ball(F(1,2)).exp()*300**6*(-arb(150)).exp()
             *2*(-arb(150)).exp())
    assert pi > 3 and (-ball(F(3,2)*21)).exp() < ball(F(1,2))
    tail = arb(0,bound.upper())

    def jets(r, orders):
        a = pi*(2*r).exp()
        out = {j:tail for j in orders}
        for n in range(1,10):
            x = a*n*n
            w = (r/2-x).exp()
            for j in orders:
                p = arb(0)
                for c in reversed(coeffs[j]):
                    p = p*x+c
                out[j] += w*p
        return out

    origin = jets(arb(0),[0,2])
    threshold = -origin[2]/(2*origin[0])
    assert origin[0]>0 and threshold>9 and threshold<10
    assert (pi*arb(2).exp())>23
    # For r >= 1, X >= pi*exp(2)*r > 23r. Logarithmic derivative of
    # a deformed summand is 2 lambda r + 5/2 + 4X/(2X-3) - 2X < 0.
    records = []
    def cover(left,right,near):
        r = ball(left).union(ball(right))
        if near:
            j = jets(r,[2,3,4])
            test = j[4]+2*threshold*(3*j[2]+r*j[3])
        else:
            j = jets(r,[0,1])
            test = j[1]+2*threshold*r*j[0]
        if test<0:
            records.append([str(left),str(right),'q_third' if near else 'q',str(test.upper())])
            return
        if right-left < F(1,2**21):
            raise ValueError((left,right,near,str(test)))
        mid = (left+right)/2
        cover(left,mid,near)
        cover(mid,right,near)
    cover(F(0),F(1,16),True)
    cover(F(1,16),F(1),False)
    assert all(a[1]==b[0] for a,b in zip(records,records[1:]))
    assert records[0][0]=='0' and records[-1][1]=='1'
    return dict(precision=bits,critical=str(threshold),tail_bound=str(bound),cells=records)

if __name__=='__main__':
    results = [run(bits) for bits in (128,192)]
    for result in results:
        print(result['precision'],result['critical'],len(result['cells']))
    with open('d3-results.json','w') as f:
        json.dump(results,f,indent=1)
