"""Reproduce the ACE temporal-parity analysis from original PCM or project spectra."""
import argparse
import bz2
import hashlib
import io
import json
from pathlib import Path
import urllib.request
import wave
import zipfile

import numpy as np

FS = 48000
FREQ = np.arange(200, 1601)
SPEED = 343.0
PCM_HASH = "c3b74ef6f234c50dabfc20aed47eb38c80d49ca2931af08751058678923c935b"
URL = "https://zenodo.org/records/6257551/files/ACE_Corpus_RIRN_Lin8Ch.tbz2"
MEMBER = "Lin8Ch/Building_Lobby/1/Lin8Ch_EE_lobby_1_Noise_Fan.wav"

def download_prefix(late=False):
    # Distinct URLs avoid CDNs reusing bytes for a different Range header.
    segments = []
    for i in range(10 if late else 2):
        a = 6500000 * i
        b = a + 6499999
        request = urllib.request.Request(URL + f"?acoustic_range={a}-{b}",
                                         headers={"Range": f"bytes={a}-{b}"})
        with urllib.request.urlopen(request, timeout=90) as response:
            if response.status != 206 or not response.headers.get("Content-Range", "").startswith(f"bytes {a}-{b}/"):
                raise ValueError("Server did not honor Range. Extract the specified WAV from the public archive and use --wav.")
            data = response.read()
        if len(data) != b - a + 1:
            raise ValueError("Incomplete range response")
        segments.append(data)
    return b"".join(segments)

def pcm_from_prefix(prefix, late=False):
    # The bzip2 prefix ends inside a large member. Read only the requested PCM.
    raw = bz2.BZ2Decompressor().decompress(prefix)
    pos = 0
    while pos + 512 <= len(raw):
        header = raw[pos:pos+512]
        name = header[:100].split(b'\0', 1)[0].decode()
        size = int(header[124:136].strip(b'\0 '), 8)
        pos += 512
        if name == MEMBER:
            with wave.open(io.BytesIO(raw[pos:]), "rb") as wav:
                return read_wav(wav, late)
        pos += (size + 511) // 512 * 512
    raise ValueError("Selected archive prefix does not contain the target WAV")

def read_wav(wav, late=False):
    if (wav.getframerate(), wav.getnchannels(), wav.getsampwidth()) != (FS, 8, 2):
        raise ValueError("Unexpected WAV format")
    pcm = wav.readframes((96 if late else 22) * FS)
    fingerprint = "a178bccb8ef114051468fef0188b2efab808e31ce8dd5897119836d65d4caf39" if late else PCM_HASH
    if hashlib.sha256(pcm).hexdigest() != fingerprint:
        raise ValueError("Public PCM checksum mismatch")
    return np.frombuffer(pcm, dtype="<i2").reshape(-1, 8)

def form_spectra(pcm, late=False):
    def spectrum(a, b):
        x = pcm[a*FS:b*FS].reshape(b-a, FS, 8).astype(float)
        x = (x - x.mean(axis=1, keepdims=True)) * np.hanning(FS)[None,:,None]
        h = np.fft.rfft(x, axis=1)[:, FREQ, :]
        return np.einsum("bfi,bfj->fij", h.conj(), h) / (b-a)
    blocks = {"all":(64,96), "early":(64,80), "late":(80,96)} if late else {"all":(14,22), "early":(14,18), "late":(18,22)}
    blocks["training"] = (2,10)
    return {key:spectrum(a,b) for key,(a,b) in blocks.items()}

def odd_summaries(spec, weights):
    p = spec * weights[:,None,None]
    sd = np.sqrt(np.real(p.sum(0).diagonal()))
    p = p / (sd[:,None] * sd[None,:])[None,:,:]
    lags = {}
    for step in (1,2):
        tau = np.sqrt(3) * 0.06 * step / (2 * SPEED)
        phase = np.exp(2j * np.pi * FREQ * tau)
        s = np.diagonal(p, step, axis1=1, axis2=2)
        plus = (s * phase[:,None]).sum(0).real
        minus = (s * phase.conj()[:,None]).sum(0).real
        values = (plus - minus) / 2
        assert np.allclose(values, -(s.imag * phase.imag[:,None]).sum(0))
        lags[step] = values
    return lags

def analyze(spectra):
    meanspec = spectra["training"].diagonal(axis1=1, axis2=2).real.mean(1)
    results = {}
    for method, weights in [("eq", 1/meanspec), ("native", np.ones(len(FREQ)))]:
        train = odd_summaries(spectra["training"], weights)
        means = {k:float(v.mean()) for k,v in train.items()}
        record = {"training_by_spacing": means}
        for block in ("all","early","late"):
            obs = odd_summaries(spectra[block], weights)
            record[block] = {
                "measured_by_spacing": {k:float(v.mean()) for k,v in obs.items()},
                "raw_samples": {k:v.tolist() for k,v in obs.items()},
                "mae": {name:float(np.mean(np.concatenate([abs(v-sign*means[k]) for k,v in obs.items()])))
                        for name,sign in [("zero",0),("train",1),("reversed_train",-1)]}}
        results[method] = record
    return results

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    options = parser.add_mutually_exclusive_group(required=True)
    options.add_argument("--download", action="store_true", help="Fetch 13 MB for short or 65 MB for later test")
    options.add_argument("--prefix", type=Path, help="First 13,000,000 bytes, or 65,000,000 bytes with --late")
    options.add_argument("--wav", type=Path, help="Extracted original 48-kHz eight-channel WAV")
    options.add_argument("--spectra", type=Path, help="fan_short_spectra.npz from the project archive")
    options.add_argument("--project-zip", type=Path, help="GENESIS-Nonprime-Physics-Tests.zip")
    parser.add_argument("--output", type=Path, required=True, help="Output JSON path")
    parser.add_argument("--late", action="store_true", help="Test 64–96 s with the original 2–10 s calibration")
    args = parser.parse_args()
    if args.wav:
        with wave.open(str(args.wav)) as wav:
            spectra = form_spectra(read_wav(wav, args.late), args.late)
    elif args.spectra or args.project_zip:
        if args.late:
            parser.error("the previous project spectra contain only the short primary test")
        if args.project_zip:
            with zipfile.ZipFile(args.project_zip) as z:
                raw = z.read("fan_short_spectra.npz")
        else:
            raw = args.spectra.read_bytes()
        with np.load(io.BytesIO(raw), allow_pickle=False) as z:
            spectra = {k:z[k] for k in ("training","all","early","late")}
    else:
        prefix = download_prefix(args.late) if args.download else args.prefix.read_bytes()
        spectra = form_spectra(pcm_from_prefix(prefix, args.late), args.late)
    output = analyze(spectra)
    args.output.write_text(json.dumps(output, indent=2) + "\n")

if __name__ == "__main__":
    main()
