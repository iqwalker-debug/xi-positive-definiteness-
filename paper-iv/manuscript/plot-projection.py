"""Numerical illustrations of strict projection and a bounded-spectrum equality case."""
from pathlib import Path
import numpy as np
from scipy.special import spherical_jn
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from numpy.polynomial import Polynomial
from scipy.integrate import trapezoid
r=Path(__file__).resolve().parent
ink='#173746';teal='#08796f';copper='#b4562c';slate='#5b7187';bg='#fbfaf5';grey='#526670'
plt.rcParams.update({'font.family':'DejaVu Sans','text.color':ink,'axes.labelcolor':ink,'xtick.color':grey,'ytick.color':grey,'axes.facecolor':bg,'figure.facecolor':bg,'axes.spines.top':False,'axes.spines.right':False,'legend.frameon':False})
k=np.linspace(0,2.5,18001)
X=np.pi*np.arange(1,9)[:,None]**2*np.exp(2*k)
p=Polynomial([0,-3,2]);ds=[]
for _ in range(3):
    ds.append((np.exp(k/2-X)*p(X)).sum(0));p=Polynomial([.5,-2])*p+Polynomial([0,2])*p.deriv()
norm=trapezoid(ds[0],k)
w=[ds[0]/norm,-k*ds[1]/norm,(k*k*ds[2]-k*ds[1])/(3*norm)]
theta=np.linspace(0,2*np.pi,481);u=np.stack((np.cos(theta),np.sin(theta)))
def omega(dim,z):
    if dim==1:return np.cos(z)
    if dim==3:return np.sinc(z/np.pi)
    return np.where(z==0,1,3*spherical_jn(1,z)/np.where(z==0,1,z))
bounds=[];supports=[]
for d,weight in zip([1,3,5],w):
    assert abs(trapezoid(weight,k)-1)<1e-9
    V=np.stack((omega(d,8*k),omega(d,16*k)))
    coords=[];h=[]
    for v in u.T:
        g=v[0]*V[0]+v[1]*V[1]
        h.append(trapezoid(abs(g)*weight,k))
        coords.append(trapezoid(V*(weight*np.sign(g)),k,axis=1))
    bounds.append(np.array(coords));supports.append(h)
assert np.min(np.asarray(supports)[:-1]-np.asarray(supports)[1:])>0
assert abs(supports[0][60]*np.sqrt(2)-.929455431236495)<1e-6
f,(a,b)=plt.subplots(1,2,figsize=(10,5.2))
f.subplots_adjust(left=.09,right=.97,top=.74,bottom=.19,wspace=.34)
f.text(.06,.94,'FIXED SPATIAL SPECTRA   /   PROJECTION TESTS',fontsize=9,color=teal,weight='bold')
f.text(.06,.848,'Where the dimension constraint becomes strict',fontsize=20.5,weight='bold')
for d,pts,color in zip([1,3,5],bounds,[slate,teal,copper]):
    a.fill(pts[:,0],pts[:,1],color=color,alpha=.10)
    a.plot(pts[:,0],pts[:,1],c=color,lw=1.9,label=f'{d}D')
a.scatter([.5],[.5],marker='x',s=32,c='#9b3c34',zorder=5)
a.set(xlabel='Correlation at separation 8',ylabel='Correlation at separation 16',aspect='equal',xlim=(-.74,.74),ylim=(-.74,.74))
a.set_title('Xi · joint readings at one delay',fontsize=11,loc='left',weight='bold');a.legend(ncol=3,fontsize=8,loc='lower center');a.grid(alpha=.15)
x=np.linspace(.001,5,501);n=np.floor((x+np.pi/2)/np.pi);I=2*n+(-1.)**n*np.sin(x)
b.plot(x,I/x,c=copper,label='1D projection',lw=2.6);b.plot(x,abs(np.sinc(x/np.pi)),'--',c=teal,label='3D shell',lw=2)
b.axvline(np.pi/2,c=slate,ls=':',lw=1.1);b.text(1.64,.17,'π/2',fontsize=9,color=slate)
b.scatter([np.pi,np.pi],[2/np.pi,0],s=17,c=[copper,teal],zorder=6)
b.set(xlabel='Separation a  (unit frequency radius)',ylabel='Sharp maximum correlation',xlim=(0,5),ylim=(-.04,1.05));b.set_title('Control · one frequency shell',loc='left',fontsize=11,weight='bold');b.legend(loc='upper right',fontsize=8);b.grid(axis='y',alpha=.18)
f.text(.06,.062,'Left: sampled Xi boundaries. The cross marks (0.5, 0.5). Right: exact formulas agree up to π/2, then separate.',fontsize=8.8,color=grey)
f.savefig(r/'review-regions.png',dpi=170);plt.close(f)
