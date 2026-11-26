"""Approximate plotted curves. Exact highlighted values come from the Arb certificates."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.special import spherical_jn, factorial2
from numpy.polynomial import Polynomial
R=Path(__file__).resolve().parent
ink='#19364b';teal='#08786d';gold='#af4f28';navy='#304c87';sub='#4b6470';bg='#fbfaf6'
plt.rcParams.update({'font.family':'DejaVu Sans','axes.spines.right':False,'axes.spines.top':False,'figure.facecolor':bg,'axes.facecolor':bg,'axes.edgecolor':'#b7c8c4','text.color':ink,'axes.labelcolor':ink,'xtick.color':sub,'ytick.color':sub,'legend.frameon':False})
r=np.linspace(0,2.5,14001)
def integ(z): return np.trapezoid(z,x=r)
X=np.pi*np.arange(1,9)[:,None]**2*np.exp(2*r)
p=Polynomial([0,-3,2]); ds=[]
for j in range(5):
    ds.append((np.exp(r/2-X)*p(X)).sum(axis=0))
    p=Polynomial([.5,-2])*p+Polynomial([0,2])*p.deriv()
normal=integ(ds[0]);ds=[x/normal for x in ds]
wave=[ds[0],-r*ds[1],(r*r*ds[2]-r*ds[1])/3,(-r**3*ds[3]+3*r*r*ds[2]-3*r*ds[1])/15,(r**4*ds[4]-6*r**3*ds[3]+15*r*r*ds[2]-15*r*ds[1])/105]
assert all(abs(integ(x)-1)<1e-7 for x in wave)
angles=np.linspace(.01,16,261); out=[]
for m,w in enumerate(wave):
    row=[]
    for a in angles:
        z=np.maximum(a*r,1.e-12)
        omega=np.cos(z) if m==0 else factorial2(2*m-1)*spherical_jn(m-1,z)/z**(m-1)
        row.append(integ(w*np.abs(omega)))
    out.append(row)
plotcheck=np.array(out)
assert np.max(plotcheck[1:]-plotcheck[:-1])<2e-7
def head(f,k,t,s):
    f.text(.075,.938,k,color=teal,size=9,weight='bold');f.text(.075,.855,t,size=21,weight='bold')
    f.text(.075,.799,s,size=10,color=sub)
f,ax=plt.subplots(figsize=(9,5.3))
f.subplots_adjust(left=.11,right=.96,top=.72,bottom=.19)
head(f,'FIGURE 1    /    SHARP COVARIANCE BOUNDS','The same snapshot permits different futures','Maximum possible delayed correlation under full spatial isotropy. The time lag is fixed and nonzero.')
for row,dim,col,style in zip(out,[1,3,5,7,9],[gold,teal,navy,'#806a9e','#688278'],['-','-','--','-.',':']):
    ax.plot(angles,row,label=f'd = {dim}',color=col,ls=style,lw=2)
ax.scatter([5,5],[.6690408010550753,.557929001287916],s=25,color=[gold,teal],zorder=8)
ax.set(xlabel='Spatial separation a  (dimensionless Xi units)',ylabel='Sharp bound  H$_d$(a)',xlim=(0,16),ylim=(0,1.035))
ax.grid(axis='y',color='#dce5df');ax.legend(loc='upper right',ncol=2,fontsize=9)
f.text(.075,.060,'Odd dimensions shown. The proof also orders every intervening even dimension. Dots at a = 5 have Arb certificates.',size=8.5,color=sub)
f.savefig(R/'envelopes.png',dpi=190);plt.close(f)
