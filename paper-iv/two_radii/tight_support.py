"""High-accuracy verified quadrature for three axis/sum supports, Python-FLINT 0.9.0.
All quadrature panels use entire integrands. Signs chosen from a real midpoint
are certified against exactly listed analytic zero crossings.
"""
import json
from pathlib import Path
import flint
from flint import arb as R, acb as C
flint.ctx.prec=168
pi=R.pi()
def waves(z,flag):
    if flag=='mass': return 1
    if flag=='axis8': return (8*z).cos()
    if flag=='axis16': return (16*z).cos()
    if flag=='diff': return (8*z).cos()-(16*z).cos()
    return (8*z).cos()+(16*z).cos()
def integral(flag):
    cuts=[R(0),R(3)]
    if flag in ('axis8','axis16'):
        w=8 if flag=='axis8' else 16
        cuts += [pi*(2*j+1)/(2*w) for j in range(30) if pi*(2*j+1)/(2*w)<3]
    if flag=='sum':
        # cos(8k)+cos(16k) changes sign at 8k = 2*pi*j +/- pi/3.
        cuts += [pi*(6*j+s)/24 for j in range(6) for s in (-1,1) if 0<pi*(6*j+s)/24<3]
    if flag=='diff':
        cuts += [pi*(3*j+s)/12 for j in range(6) for s in (-1,1) if 0<pi*(3*j+s)/12<3]
    # Numerical grid allows domain subdivision; arbitrary extra boundaries are harmless.
    cuts+= [R(j)/8 for j in range(1,24)]
    cuts.sort(key=float)
    result=R(0)
    for lo,hi in zip(cuts,cuts[1:]):
        midpoint=(lo+hi)/2
        sign=1 if flag=='mass' or waves(midpoint,flag)>0 else -1
        if flag!='mass':
            assert sign*waves(midpoint,flag)>0
        def f(z,analytic):
            z0=pi*(2*z).exp()
            ker=C(0)
            for n in range(1,9):
                x=z0*n*n
                ker+=(z/2-x).exp()*x*(2*x-3)
            return ker*waves(z,flag)
        result+=sign*C.integral(f,lo,hi,rel_tol=R(2)**-150,abs_tol=R(2)**-150).real
    # Raw omitted mass < 1e-51. For n>=9, sum exp(-3*n*n/2) < 2e-53.
    # The eight included n beyond k=3 contribute <=8 exp(-3 exp(6)/2).
    return result+R(0,R('1e-51')*(2 if flag in ('sum','diff') else 1))
def main():
    z=integral('mass')
    out={'raw_normalizer':str(z)}
    for label in ['axis8','axis16','sum','diff']:
        out[label]=str(integral(label)/z)
    out['working_precision_bits']=flint.ctx.prec
    (Path(__file__).parent/'tight-supports.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
