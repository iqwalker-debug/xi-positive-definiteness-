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

`results_from_pcm.json` and `late_results.json` hold the original cross-spectral replay results. `independent.json` records the independent approach using synthesized time-shifted signals and inner products. `comparison.json` reports the maximum absolute difference of the paired values. The project records its choices for these two observation windows in `protocol.txt` and `late_protocol.txt`. These files document the analysis sequence. No independently dated preregistration is supplied.

## Seven windows in the same recording

The sensitivity analysis divides the intervening audio into five consecutive eight-second windows beginning at 22 s. The intervals are [22,30), [30,38), [38,46), [46,54) and [54,62) seconds. The two seconds before the 64–96 s original holdout do not form a sixth full window. All five windows are post hoc. The two spacing means and the inverse-power equalizer remain fixed at their 2–10 s training values. The same analysis also uses uniform weights on 200–1,600 Hz. Each window uses its own channel powers to normalize the band-limited correlations, following the original estimator.

`window-results.json` stores the signed odd correlations of all 13 pairs, counts of positive pairs, pairwise forward wins against zero, and the mean absolute error of each predictor. Each of the 13 pairs carries equal weight in the error calculation. Within `odd_pairs`, the first seven entries represent channel pairs 1–2 through 7–8, and the last six represent pairs 1–3 through 6–8. The same pairs and time windows enter both weightings.

At 54–62 s all 13 measured correlations were negative with each weighting. In the training-equalized band the reversed, zero and forward predictors had errors of 0.03501, 0.08961 and 0.14421. The corresponding uniform-band errors were 0.03457, 0.07065 and 0.10673. The forward predictor had the lowest aggregate error in the other six windows. These temporal changes describe one recording from one array.

Run the commands below from this directory. The offline command recalculates all published-window and sensitivity-window scores from the committed pairs and compares the two original windows with their separate replay files. The raw command verifies the input PCM hash, regenerates the seven windows and checks all values against the committed file. At 54–62 s it independently reconstructs time-shifted channel signals and compares all 26 pair-weight observations and six aggregate errors with the frequency-domain implementation. The absolute comparison tolerance is 5 × 10⁻¹³. The plotting command requires Matplotlib and writes `../manuscript/acoustic-windows.png`.

```sh
python replay_windows.py --check-stored
python replay_windows.py --source /path/to/Lin8Ch_EE_lobby_1_Noise_Fan.wav
python plot_windows.py
```

For a fresh copy of the computed JSON, add `--output rerun-windows.json` to the raw command. A signed 16-bit PCM NumPy array with the same channel order and checksum is also accepted. The `--download` option retrieves just the required archive prefix when the data provider supports HTTP Range requests.
