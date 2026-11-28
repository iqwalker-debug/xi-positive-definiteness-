"""Non-interval quadrature. Push forward the common signed-frequency density f9 by coordinate projection."""
from pathlib import Path
from math import factorial,pi
import numpy as np
import mpmath as mp
from scipy.special import gamma, jv, roots_legendre
from scipy.optimize import brentq
import csv
mp.mp.dps=65
p=[[mp.mpf(0),mp.mpf(-3),mp.mpf(2)]]
for j in range(40):
 c=p[-1]; v=[mp.mpf(0)]*(len(c)+1)
 for k,ck in enumerate(c):
  v[k]+=(mp.mpf('.5')+2*k)*ck;v[k+1]-=2*ck
 p.append(v)
sig=mp.mpf('.5')
xi=sig*(sig-1)*mp.pi**(-sig/2)*mp.gamma(sig/2)*mp.zeta(sig)/2
Z=float(xi/2)
series=[]
for m in range(4,21):
 coef=mp.fsum(mp.exp(-mp.pi*n*n)*mp.polyval(p[2*m][::-1],mp.pi*n*n) for n in range(1,15))/factorial(2*m)
 series.append(float(coef*factorial(m)/factorial(m-4)/(mp.pi**4*xi/2)))
coef=[np.array(row,dtype=float) for row in p[:5]]
def f9(r):
 arr=np.asarray(r)
 A=arr>=.13; x=arr[A]; tot=np.zeros_like(x)
 for n in range(1,6):
  X=pi*n*n*np.exp(2*x)
  P=[np.polynomial.polynomial.polyval(X,c) for c in coef]
  T=x**3*P[4]-6*x**2*P[3]+15*x*P[2]-15*P[1]
  tot+=np.exp(x/2-X)*T
 ans=np.empty_like(arr)
 ans[A]=tot/((2*pi)**4*Z*x**7)
 ans[~A]=np.polynomial.polynomial.polyval(arr[~A]**2,series)
 return ans
def area(dim):
 return 2*pi**(dim/2)/gamma(dim/2)
def angular(d,x):
 if d==1:return np.cos(x)
 if d==3:return np.sinc(x/np.pi)
 return gamma(d/2)*(2/x)**(d/2-1)*jv(d/2-1,x)
def calc(d,a,order,cutoff):
 node,weight=roots_legendre(order)
 v=(node+1)*cutoff/2;wv=weight*cutoff/2
 def radial(u):
  if d==9:return area(d)*u**(d-1)*f9(u)
  f=f9(np.sqrt(u[:,None]**2+v[None,:]**2))
  return area(d)*u**(d-1)*area(9-d)*np.sum(f*(v**(8-d)*wv),axis=1)
 breaks=[0.]
 if a>0:
  span=np.arange(.001,a*cutoff,.20)
  pairs=zip(span[:-1],span[1:])
  for lo,hi in pairs:
   if angular(d,lo)*angular(d,hi)<0:breaks.append(brentq(lambda x:angular(d,x),lo,hi)/a)
 breaks.append(cutoff)
 vals=[]
 for lo,hi in zip(breaks,breaks[1:]):
  u=lo+(hi-lo)*(node+1)/2;weights=weight*(hi-lo)/2
  q=angular(d,a*u) if a else np.ones_like(u)
  den=radial(u)
  vals.append([np.sum(weights*den),np.sum(weights*den*q),np.sum(weights*den*abs(q))])
 return np.sum(vals,axis=0)
def direct(a):
 s=mp.mpc(.5,a)
 return float(mp.re(s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)/2/xi))
with Path(__file__).with_name('gennew-ladder.csv').open('w') as out:
 w=csv.writer(out);w.writerow(['d','a','B_d','coarse_B','abs_refine_difference','mass_error','abs_Xi_transform_error'])
 for a in [5,8]:
  for d in range(1,10):
   small=calc(d,a,60,2.4)
   hi=calc(d,a,105,2.65)
   result=[d,a,hi[2],small[2],abs(small[2]-hi[2]),abs(hi[0]-1),abs(hi[1]-direct(a))]
   print(*result,flush=True)
   w.writerow(result);out.flush()
