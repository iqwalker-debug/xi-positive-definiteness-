"""Reproduce the ACE window-sensitivity table, including all 13 oriented pairs."""
import argparse
import json
from pathlib import Path

import numpy as np

from pcm_inner_product import compute, load_pcm
from replay import FREQ, download_prefix, odd_summaries, pcm_from_prefix, spectrum

HERE = Path(__file__).resolve().parent
STORED = HERE / "window-results.json"
PCM_HASH = "a178bccb8ef114051468fef0188b2efab808e31ce8dd5897119836d65d4caf39"
TRAIN = (2, 10)
INTERVALS = [(14, 22), (22, 30), (30, 38), (38, 46), (46, 54), (54, 62), (64, 96)]
ORIGINAL = {(14, 22): "results_from_pcm.json", (64, 96): "late_results.json"}
METHODS = {"equalized": "eq", "native": "native"}
ATOL = 5e-13


def pair_scores(observed, means):
    predictor = np.repeat(means, [7, 6])
    return {
        "mae": {key: float(np.mean(abs(observed - sign * predictor)))
                for key, sign in [("zero", 0), ("forward", 1), ("reversed", -1)]},
        "positive_pairs": int(np.count_nonzero(observed > 0)),
        "forward_wins": int(np.count_nonzero(abs(observed - predictor) < abs(observed))),
        "odd_pairs": observed.tolist(),
    }


def replay(pcm):
    training = spectrum(pcm, *TRAIN)
    power = training.diagonal(axis1=1, axis2=2).real.mean(axis=1)
    weights = {"equalized": 1 / power, "native": np.ones_like(power)}
    means = {}
    for name, w in weights.items():
        pairs = odd_summaries(training, w)
        means[name] = [float(pairs[step].mean()) for step in (1, 2)]
    windows = []
    for start, end in INTERVALS:
        current = spectrum(pcm, start, end)
        scores = {}
        for name, w in weights.items():
            pairs = odd_summaries(current, w)
            scores[name] = pair_scores(np.concatenate([pairs[1], pairs[2]]), means[name])
        windows.append({"start": start, "end": end,
                        "role": "reported" if (start, end) in ORIGINAL else "post_hoc",
                        "weightings": scores})
    return {"pcm_sha256": PCM_HASH, "training_seconds": list(TRAIN),
            "frequency_hz": [int(FREQ[0]), int(FREQ[-1])], "training_means": means, "windows": windows}


def compare(actual, expected, path="results"):
    """Compare all keys, exact labels and counts, and numerical arrays within tolerance."""
    if isinstance(expected, dict):
        if actual.keys() != expected.keys():
            raise ValueError(f"Different fields in {path}")
        for k, value in expected.items():
            compare(actual[k], value, f"{path}.{k}")
    elif isinstance(expected, list) and expected and isinstance(expected[0], dict):
        if len(actual) != len(expected):
            raise ValueError(f"Different lengths in {path}")
        for i, (a, e) in enumerate(zip(actual, expected)):
            compare(a, e, f"{path}[{i}]")
    elif isinstance(expected, (float, list)):
        np.testing.assert_allclose(actual, expected, atol=ATOL, rtol=0, equal_nan=False, err_msg=path)
    elif actual != expected:
        raise ValueError(f"Different value in {path}")


def check_stored(data):
    compare(data["pcm_sha256"], PCM_HASH)
    compare(data["training_seconds"], list(TRAIN))
    compare(data["frequency_hz"], [200, 1600])
    intervals = [(row["start"], row["end"]) for row in data["windows"]]
    if intervals != INTERVALS or data["training_means"].keys() != METHODS.keys():
        raise ValueError("Unexpected windows or weightings")
    for row in data["windows"]:
        interval = (row["start"], row["end"])
        archived = json.loads((HERE / ORIGINAL[interval]).read_text()) if interval in ORIGINAL else None
        compare(row["role"], "reported" if archived else "post_hoc")
        if row["weightings"].keys() != METHODS.keys():
            raise ValueError("Unexpected weightings")
        for name, original_name in METHODS.items():
            means = data["training_means"][name]
            entry = row["weightings"][name]
            obs = np.asarray(entry["odd_pairs"])
            if obs.shape != (13,) or not np.isfinite(obs).all():
                raise ValueError("Expected 13 finite pair values")
            compare(entry, pair_scores(obs, means))
            if archived:
                old = archived[original_name]
                compare(means, [old["training_by_spacing"][d] for d in ("1", "2")])
                pairs = old["all"]["raw_samples"]
                compare(obs, pairs["1"] + pairs["2"])
                for new, prior in [("zero", "zero"), ("forward", "train"), ("reversed", "reversed_train")]:
                    compare(entry["mae"][new], old["all"]["mae"][prior])


def cross_check_reversal(pcm, data):
    direct = compute(pcm, {"reversal": (54, 62)})
    target = next(row for row in data["windows"] if row["start"] == 54)
    errors = []
    for name, original_name in METHODS.items():
        record = direct[original_name]["reversal"]
        pairs = record["pairs"]["1"] + record["pairs"]["2"]
        entry = target["weightings"][name]
        compare(entry["odd_pairs"], pairs)
        errors.extend(abs(np.asarray(entry["odd_pairs"]) - pairs))
        for new, prior in [("zero", "zero"), ("forward", "train"), ("reversed", "reversed_train")]:
            compare(entry["mae"][new], record["mae"][prior])
    return max(errors)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--source", type=Path, help="original WAV or signed PCM .npy in channel order")
    inputs.add_argument("--download", action="store_true", help="read a prefix of the public ACE archive")
    inputs.add_argument("--check-stored", action="store_true", help="offline arithmetic and original-holdout checks")
    parser.add_argument("--output", type=Path, help="write recomputed values to this JSON file")
    args = parser.parse_args()
    if args.check_stored:
        if args.output:
            parser.error("--output requires --source or --download")
        check_stored(json.loads(STORED.read_text()))
        print("Verified 7 windows, 2 weightings, 13 pairs and both original holdout files.")
        return
    pcm = (load_pcm(args.source)[0] if args.source else
           pcm_from_prefix(download_prefix(late=True), late=True))
    result = replay(pcm)
    check_stored(result)
    discrepancy = cross_check_reversal(pcm, result)
    print(f"54–62 s time-domain check: all 26 pair values agree, maximum difference {discrepancy:.3g}.")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
    else:
        compare(result, json.loads(STORED.read_text()))
        print("All seven recomputed windows agree with window-results.json.")


if __name__ == "__main__":
    main()
