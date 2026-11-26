# Acoustic parity control

The ACE study tests the oriented, odd-in-time component of cross-correlations in one room with one eight-microphone array. The data were collected by James Eaton, Nikolay D. Gaubitch, Alastair H. Moore and Patrick A. Naylor. Their archive `ACE_Corpus_RIRN_Lin8Ch.tbz2` contains the WAV member `Lin8Ch/Building_Lobby/1/Lin8Ch_EE_lobby_1_Noise_Fan.wav`. [Dataset and microphone diagrams](https://doi.org/10.5281/zenodo.6257551) · [ACE Challenge article](https://doi.org/10.1109/TASLP.2016.2577502)

With Python 3 and NumPy, run the following commands from this directory, using the filesystem path to the extracted WAV:

```sh
python replay.py --wav /path/to/Lin8Ch_EE_lobby_1_Noise_Fan.wav --output short.json
python replay.py --wav /path/to/Lin8Ch_EE_lobby_1_Noise_Fan.wav --late --output late.json
python pcm_inner_product.py /path/to/Lin8Ch_EE_lobby_1_Noise_Fan.wav > independent-rerun.json
```

Alternatively, replace `--wav /path/to/...` with `--download` in the first two commands. The public data provider must honor HTTP Range requests for this option. The scripts check the initial little-endian signed PCM in its original channel order before analysis.

| PCM segment | SHA-256 |
|---|---|
| 22 s | `c3b74ef6f234c50dabfc20aed47eb38c80d49ca2931af08751058678923c935b` |
| 96 s | `a178bccb8ef114051468fef0188b2efab808e31ce8dd5897119836d65d4caf39` |

The 2–10 s training interval sets the mean by separation. The estimates are held fixed in the 14–22 s and 64–96 s comparisons. Each held-out interval includes seven increasing-index adjacent pairs at 6 cm and six second-neighbor pairs at 12 cm, using both the 200–1600 Hz training equalizer and uniform band weights. The 52 pairwise results are correlated measurements in the same recording. The observable is an acoustic symmetry diagnostic.

`results_from_pcm.json` and `late_results.json` hold the original cross-spectral replay results. `independent.json` records the independent approach using synthesized time-shifted signals and inner products. `comparison.json` reports the maximum absolute difference of the paired values. The frozen choices for the two observation windows appear in `protocol.txt` and `late_protocol.txt`.
