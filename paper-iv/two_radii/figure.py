"""Render the deterministic covariance-region figure after running geometry.py."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
p=Path(__file__).parent
r=json.loads((p/'joint-results.json').read_text())
q=np.genfromtxt(p/'joint-boundary.csv',delimiter=',',names=True)
G=np.array(r['G_reflected_local_spatial_gram']);phi=np.linspace(0,2*np.pi,600)
ell=np.linalg.cholesky(G)@np.array([np.cos(phi),np.sin(phi)])
h=r['supports']['1,1']['h'];b1=r['supports']['1,0']['h'];b2=r['supports']['0,1']['h']
fig,ax=plt.subplots(figsize=(5.6,4.3));slate='#52637c';teal='#197d78';red='#b04c2c'
ax.fill(q['boundary_C8'],q['boundary_C16'],facecolor='#c7e6de',edgecolor=teal,linewidth=1.7,label='Admissible joint correlations',zorder=2)
ax.plot(ell[0],ell[1],color=slate,linestyle='--',lw=1.2,label='Local covariance ellipse')
ax.add_patch(Rectangle((-b1,-b2),2*b1,2*b2,fill=False,linestyle=':',edgecolor='#68798e',linewidth=1.15,label='Individual bounds'))
ax.plot([.19,.72],[h-.19,h-.72],lw=1.3,color=teal,zorder=3)
ax.scatter(.5,.5,marker='x',color=red,linewidth=2.2,s=65,zorder=5,label='Excluded pair (0.5, 0.5)')
ax.scatter(*r['supports']['1,1']['attaining_pair'],color=teal,s=19,zorder=4)
ax.set_xlabel('Correlation at spatial offset 8');ax.set_ylabel('Correlation at spatial offset 16')
ax.set_xlim(-.78,.78);ax.set_ylim(-.78,.78);ax.set_aspect('equal')
ax.axvline(0,lw=.6,color='#b8c5cb',zorder=0);ax.axhline(0,lw=.6,color='#b8c5cb',zorder=0)
ax.spines[['top','right']].set_visible(False);ax.legend(loc='upper center',bbox_to_anchor=(.5,-.18),ncols=2,frameon=False,fontsize=7.8)
fig.tight_layout()
fig.savefig(p.parent/'manuscript'/'joint-region.png', dpi=230, bbox_inches='tight')
