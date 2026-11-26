"""Independent ACE check by time-domain inner products on phase-shifted audio.
Supply 96 seconds of the original eight-channel PCM in WAV or integer NPY.
The archive DOI, source WAV member and fingerprints are in README.md.
"""
from pathlib import Path
from argparse import ArgumentParser
import hashlib, json, wave
import numpy as np

FS=48000
def load_pcm(path):
    if path.suffix == '.npy':
        x=np.load(path, mmap_mode='r',allow_pickle=False)
    else:
        with wave.open(str(path)) as w:
            if (w.getframerate(),w.getnchannels(),w.getsampwidth()) != (FS,8,2):
                raise ValueError('Expected 48 kHz, 16-bit, eight-channel input')
            x=np.frombuffer(w.readframes(96*FS),dtype='<i2').reshape(-1,8)
    if x.shape[0] < 96*FS or x.shape[1] != 8:
        raise ValueError('96 s of eight-channel data required')
    x=x[:96*FS];h=hashlib.sha256(np.asarray(x,dtype='<i2').tobytes()).hexdigest()
    if h != 'a178bccb8ef114051468fef0188b2efab808e31ce8dd5897119836d65d4caf39':
        raise ValueError('PCM SHA-256 differs')
    return x,h

def compute(x):
    band=np.arange(200,1601)
    window=np.hanning(FS)[:,None]
    def select(s):
        frame=np.array(x[s*FS:(s+1)*FS],dtype=float)
        return np.fft.rfft((frame-frame.mean(axis=0))*window,axis=0)[band]
    power=sum(np.mean(np.abs(select(s))**2,axis=1) for s in range(2,10))/8
    output={}
    def synth(H):
        buf=np.zeros((1+FS//2,8),dtype=complex);buf[band]=H
        return np.fft.irfft(buf,n=FS,axis=0)
    for key,w in [('eq',1/np.sqrt(power)),('native',np.ones_like(power))]:
        sets={}
        for block,(lo,hi) in {'train':(2,10),'short':(14,22),'late':(64,96)}.items():
            den=np.zeros(8)
            odd={step:np.zeros(8-step) for step in (1,2)}
            reverse={step:np.zeros(8-step) for step in (1,2)}
            for s in range(lo,hi):
                spec=w[:,None]*select(s)
                ref=synth(spec)
                den+=np.einsum('ij,ij->j',ref,ref)
                for step in (1,2):
                    tau=np.sqrt(3)*step*.06/(2*343)
                    # (j advanced - j delayed)/2 as an actual time series.
                    contrast=synth(spec*(1j*np.sin(2*np.pi*band*tau))[:,None])
                    odd[step]+=np.einsum('ij,ij->j',ref[:,:-step],contrast[:,step:])
                    reverse[step]+=np.einsum('ij,ij->j',ref[:,step:],contrast[:,:-step])
            for step in odd:
                scale=np.sqrt(den[:-step]*den[step:])
                odd[step]/=scale; reverse[step]/=scale
                if np.max(np.abs(odd[step]+reverse[step]))>1e-10:
                    raise ArithmeticError('Oriented reversal check failed')
            sets[block]=odd
        training={d:sets['train'][d].mean() for d in (1,2)}
        output[key]={}
        for blk in ('short','late'):
            obs=sets[blk]
            scores={name:np.mean(np.concatenate([abs(obs[d]-sign*training[d]) for d in (1,2)]))
                    for name,sign in [('zero',0),('train',1),('reversed_train',-1)]}
            output[key][blk]={'mae':scores,'pairs':{str(d):v.tolist() for d,v in obs.items()}}
    return output
if __name__=='__main__':
    parser=ArgumentParser();parser.add_argument('source',type=Path);args=parser.parse_args()
    x,h=load_pcm(args.source)
    print(json.dumps({'pcm_sha256':h,'method':'time-domain products after synthesis of symmetric band and opposite fractional lags','runs':compute(x)},indent=2))
