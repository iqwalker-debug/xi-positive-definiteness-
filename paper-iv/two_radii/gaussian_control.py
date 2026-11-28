"""Curvature-matched non-arithmetic null for the fixed-lag admissible region."""
from pathlib import Path
import json
import flint
from flint import arb as R,acb as C,acb_series as Series
flint.ctx.prec=168
pi=R.pi()
def xi(s):return s*(s-1)/2*(-s*pi.log()/2).exp()*(s/2).gamma()*s.zeta()
z=xi(Series([R(1)/2,1],prec=3))
v=2*z[2].real/z[0].real
norm=(2/(pi*v)).sqrt()
def compute(sign):
    cuts=[R(0),R(4)]+[R(j)/8 for j in range(1,32)]
    shift=1 if sign==1 else 2
    cuts += [pi*(6*j+s*shift)/24 for j in range(7) for s in (-1,1) if 0<pi*(6*j+s*shift)/24<4]
    cuts.sort(key=float)
    pair=[R(0),R(0)]
    for lo,hi in zip(cuts,cuts[1:]):
        mid=(lo+hi)/2
        fmid=(8*mid).cos()+sign*(16*mid).cos()
        flip=1 if fmid>0 else -1
        assert fmid*flip>0
        for idx,w in enumerate([8,16]):
            def f(k,analytic):return norm*(-k*k/(2*v)).exp()*(w*k).cos()
            pair[idx]+=flip*C.integral(f,lo,hi,rel_tol=R(2)**-148,abs_tol=R(2)**-148).real
    # Half-normal tail <= sqrt(2*v/pi)/T * exp(-T²/(2v)), T=4.
    mass=(2*v/pi).sqrt()/4*(-8/v).exp()
    assert mass<R('1e-74')
    pair=[q+R(0,mass) for q in pair]
    return {'axis8_coordinate':str(pair[0]),'axis16_coordinate':str(pair[1]),'support':str(pair[0]+sign*pair[1])}
obj={'variance':str(v),'sum_direction':compute(1),'difference_direction':compute(-1)}
(Path(__file__).parent/'gaussian-comparison.json').write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps(obj,indent=2))
