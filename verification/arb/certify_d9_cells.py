"""D9 sign certificate with exact rational endpoints and exported dyadic margins."""
import argparse
import hashlib
import json
import re
from pathlib import Path
from fractions import Fraction as F
from math import comb
from flint import arb, ctx, __version__ as flint_version

def need(cond,msg):
    if not cond:
        raise ArithmeticError(msg)

def ball(x):
    q=F(x)
    return arb(q.numerator)/arb(q.denominator)

def box(a,b):
    return ball(a).union(ball(b))

def sym(x):
    m=x.abs_upper()
    return (-m).union(m)

def polynomial_list():
    q=[F(0),F(-3),F(2)]
    out=[q]
    for _ in range(9):
        p=[F(0)]*(len(q)+1)
        for k,v in enumerate(q):
            p[k]+=(F(1,2)+2*k)*v
            p[k+1]-=2*v
        q=p
        out.append(q)
    return out

def coefficient_shift(q,c):
    return [sum(q[k]*comb(k,j)*c**(k-j) for k in range(j,len(q))) for j in range(len(q))]

def dyadic(x):
    n,k=x.man_exp()
    return [str(n),int(k)]

def from_dyadic(x):
    n,k=map(int,x)
    return F(n*2**k) if k>=0 else F(n,2**(-k))

class Certificate:
    def __init__(self,bits):
        ctx.prec=bits
        self.bits=bits
        self.pi=arb.pi()
        self.Q=polynomial_list()
        self.Qb=[[ball(c) for c in q] for q in self.Q]
        self.C=[ball(sum(map(abs,q))) for q in self.Q]
        self.tail=[[(-1)**j*x for x in coefficient_shift(self.Q[j],20)] for j in range(1,5)]
        need(ball(F(7,6))**22*(-13*self.pi).exp()<ball(F(1,2)),"theta tail ratio")
        need(36*self.pi>11,"theta majorant monotonicity")
        need(self.pi*arb(2).exp()>20,"far radius sign cutoff")
        need(all(c>0 for row in self.tail for c in row),"far exact shifted coefficient signs")

    def phi(self,a,b,orders):
        r=box(a,b)
        p=ball(a)
        xr=self.pi*(2*r).exp()
        x6=36*self.pi*(2*p).exp()
        common=(r/2).exp()
        tail_exp=(ball(b)/2-x6).exp()
        vals={j:arb(0) for j in orders}
        for n in range(1,6):
            x=n*n*xr
            e=(-x).exp()
            for j in orders:
                f=arb(0)
                for c in reversed(self.Qb[j]):
                    f=f*x+c
                vals[j]+=f*e
        return {j:common*vals[j]+sym(2*self.C[j]*x6**(j+2)*tail_exp) for j in orders}

    def near(self,a,b):
        c=(a+b)/2
        fc=self.phi(c,c,(8,))[8]
        db=self.phi(a,b,(9,))[9]
        return fc+sym(ball((b-a)/2)*db)

    def middle(self,a,b):
        c=(a+b)/2
        cb=ball(c)
        r=box(a,b)
        v=self.phi(c,c,(1,2,3,4))
        fc=cb**3*v[4]-6*cb**2*v[3]+15*cb*v[2]-15*v[1]
        db=self.phi(a,b,(3,4,5))
        # N'(r) after exact cancellation of first and second derivatives.
        d=r**3*db[5]-3*r**2*db[4]+3*r*db[3]
        return fc+sym(ball((b-a)/2)*d)

    def partition(self,label,a,b):
        fn=getattr(self,label)
        pending=[(a,b,0)]
        leaves=[]
        while pending:
            lo,hi,depth=pending.pop()
            v=fn(lo,hi)
            if v>0:
                low=v.lower()
                need(low>0,"positive lower endpoint")
                leaves.append(dict(left=str(lo),right=str(hi),lower_dyadic=dyadic(low),depth=depth))
            else:
                need(depth<25,f"{label} subdivision depth at {lo}..{hi}")
                mid=(lo+hi)/2
                pending.extend(((mid,hi,depth+1),(lo,mid,depth+1)))
        return leaves

    def run(self):
        near=self.partition('near',F(0),F(1,5))
        middle=self.partition('middle',F(1,5),F(1))
        payload=dict(bits=self.bits,python_flint=flint_version,near=near,middle=middle,
                     far_shifted_polynomials=[[str(c) for c in p] for p in self.tail])
        verify_structure(payload)
        return payload

def verify_structure(payload):
    for k,left,right in [('near',F(0),F(1,5)),('middle',F(1,5),F(1))]:
        rows=payload[k]
        need(bool(rows),f"{k} nonempty")
        cursor=left
        for r in rows:
            a,b=F(r['left']),F(r['right'])
            need(a==cursor and b>a,f"{k} exact gap-free ordered cover")
            need(from_dyadic(r['lower_dyadic'])>0,f"{k} positive serialized bound")
            cursor=b
        need(cursor==right,f"{k} exact right endpoint")
    p=polynomial_list()
    expected=[ [str((-1)**j*x) for x in coefficient_shift(p[j],20)] for j in range(1,5)]
    need(payload['far_shifted_polynomials']==expected,"tail exact coefficient reconstruction")
    need(all(F(x)>0 for row in expected for x in row),"tail signs")

def verify_leaves(payload):
    verify_structure(payload)
    c=Certificate(payload['bits'])
    for k in ('near','middle'):
        fn=getattr(c,k)
        for cell in payload[k]:
            v=fn(F(cell['left']),F(cell['right']))
            m,e=cell['lower_dyadic']
            exact=arb(int(m))*arb(2)**e
            need(exact>0 and v.lower()>=exact,f"{k} recomputed leaf margin")

def verify_lean_rows(payload, source):
    for region in ("near", "middle"):
        name = region + str(payload["bits"])
        section = re.search(rf"def {name} : List Cell := \[([^\]]*)\]", source)
        need(section is not None, f"Lean table {name} not found")
        parsed = [tuple(map(int, x)) for x in re.findall(
            r"⟨(\d+), (\d+), (\d+), (-?\d+)⟩", section[1])]
        expected = []
        for row in payload[region]:
            left, right = (320 * F(row[k]) for k in ("left", "right"))
            need(left.denominator == right.denominator == 1, "off-grid endpoint")
            expected.append((left.numerator, right.numerator,
                             *map(int, row["lower_dyadic"])))
        need(parsed == expected, f"fresh Arb rows differ from Lean table {name}")


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--bits',nargs='+',type=int,default=[192,256])
    parser.add_argument('--verify',nargs='+')
    parser.add_argument('--check-lean', type=Path)
    args=parser.parse_args()
    if args.verify:
        for filename in args.verify:
            with open(filename) as f:
                p=json.load(f)
            verify_leaves(p)
            print(f"{filename}: {len(p['near'])}+{len(p['middle'])} margins and exact cover PASS")
        return
    for bits in args.bits:
        p=Certificate(bits).run()
        if args.check_lean:
            verify_lean_rows(p, args.check_lean.read_text())
        data=(json.dumps(p,indent=2)+'\n').encode()
        with open(f'd9-certificate-{bits}.json','wb') as f:
            f.write(data)
        summary={k:dict(cells=len(p[k]),min_cell_lower=float(min(from_dyadic(c['lower_dyadic']) for c in p[k])),max_depth=max(c['depth'] for c in p[k])) for k in ('near','middle')}
        print(json.dumps(dict(bits=bits,regions=summary,sha256=hashlib.sha256(data).hexdigest())),flush=True)

if __name__=='__main__':
    main()
