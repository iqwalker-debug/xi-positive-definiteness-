"""Generate or check the printed Paper IV numbers. Uses only Python's standard library."""
import argparse
from collections import Counter
import csv
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN, localcontext
from fractions import Fraction
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "manuscript/manuscript.template.md"
DEPOSIT = ROOT / "manuscript/manuscript.md"
FIELD = re.compile(r"\{\{claim:([a-zA-Z0-9_.-]+)\}\}")
BALL = re.compile(r"\[([^\[\] ]+) \+/- ([^\[\] ]+)\]")


def read_json(path):
    return json.loads((ROOT / path).read_text(), parse_float=Decimal)


def arb_bounds(value):
    match = BALL.fullmatch(value)
    if not match:
        raise ValueError(f"Invalid Arb ball {value!r}")
    mid, radius = map(Decimal, match.groups())
    if not (mid.is_finite() and radius.is_finite() and radius >= 0):
        raise ValueError(f"Invalid midpoint or radius in {value!r}")
    return mid - radius, mid + radius


def fixed(value, digits, rounding=ROUND_HALF_EVEN):
    step = Decimal(1).scaleb(-digits)
    return format(value.quantize(step, rounding=rounding), "f")


def nearest(bounds, digits):
    lower, upper = bounds
    if lower > upper or fixed(lower, digits) != fixed(upper, digits):
        raise ValueError(f"Interval {bounds} does not certify a single {digits}-place value")
    return fixed(lower, digits)


def decimal_bounds(record):
    lower, upper = (Decimal(record[end]) for end in ("lower", "upper"))
    if not (lower.is_finite() and upper.is_finite() and lower < upper):
        raise ValueError(f"Invalid endpoint ordering in {record}")
    return lower, upper


def scientific(coefficient, exponent):
    return rf"{coefficient}\times10^{{{exponent}}}"


def one_lag(values):
    line = read_json("single_lag/xi_covariance_certificate.json")
    space = read_json("single_lag/d3.json")
    line_run = next(row for row in line["results"] if row["bits"] == 256)
    space_run = next(row for row in space["results"] if row["bits"] == 256)
    for row in line_run["rows"]:
        prefix = f"lag.{row['a']}."
        values[prefix + "T"] = nearest(arb_bounds(row["gram_bound"]), 9)
        values[prefix + "H1"] = nearest(arb_bounds(row["envelope"]), 9)
        if row["a"] == 5:
            values["lag.5.detailed"] = nearest(arb_bounds(row["envelope"]), 35)
    for row in space_run["rows"]:
        values[f"lag.{row['a']}.H3"] = nearest(arb_bounds(row["enclosure"]), 9)
    counter = line_run["counterexample"]
    values["lag.determinant"] = nearest(arb_bounds(counter["local_gram_determinant"]), 8)
    values["lag.excess"] = nearest(arb_bounds(counter["excess_over_global"]), 11)
    fraction = Fraction(counter["c"])
    values["lag.c"] = fixed(Decimal(fraction.numerator) / fraction.denominator, 2)
    with (ROOT / "dimension_projection/gennew-ladder.csv").open(newline="") as stream:
        for row in csv.DictReader(stream):
            if row["a"] == "8":
                values[f"dimension.{row['d']}"] = fixed(Decimal(row["B_d"]), 6)


def joint(values):
    supports = read_json("two_radii/tight-supports.json")
    for key in ("axis8", "axis16", "sum", "diff"):
        values[f"xi.{key}"] = nearest(arb_bounds(supports[key]), 10)
    example = read_json("two_radii/joint-results.json")
    pair = example["witness"]
    row = [Fraction(x) for x in example["two_time_five_site_cross_row"]]
    # These are the exact rational inputs of both matrix certificate implementations.
    if row != list(map(Fraction, ("-3/50", "1/2", "1/2", "0", "-9/25"))) or row[1:3] != pair:
        raise ValueError("The witness disagrees with the matrix checked by the determinant certificate")
    if any(x >= arb_bounds(supports[key])[0] for x, key in zip(pair, ("axis8", "axis16"), strict=True)):
        raise ValueError("The witness coordinates must be individually attainable")
    if sum(pair) <= arb_bounds(supports["sum"])[1]:
        raise ValueError("The witness sum must strictly exceed the certified Xi support")
    values["witness.row"] = ",".join(map(str, row))
    values["witness.value"] = fixed(pair[0], 2)
    values["witness.sum"] = fixed(sum(pair), 2)
    values["witness.fraction"] = str(Fraction(pair[0]))
    values["witness.margin_lower"] = fixed(sum(pair) - arb_bounds(supports["sum"])[1], 11, ROUND_FLOOR)

    gaussian = read_json("two_radii/gaussian-comparison.json")
    values["gaussian.variance"] = nearest(arb_bounds(gaussian["variance"]), 14)
    for key, direction in (("sum", "sum_direction"), ("diff", "difference_direction")):
        values[f"gaussian.{key}"] = nearest(arb_bounds(gaussian[direction]["support"]), 10)
    for axis in ("axis8", "axis16"):
        values[f"gaussian.{axis}"] = nearest(arb_bounds(gaussian["sum_direction"][axis + "_coordinate"]), 10)

    log = (ROOT / "independent-numeric/spd/eigen_certificate.log").read_text()
    block = re.search(r"^K\+J\n\s*\[(.+)\]$", log, re.M)
    if not block:
        raise ValueError("Missing first K+J Gershgorin enclosure")
    ends = [arb_bounds(item.group()) for item in BALL.finditer(block[1])]
    if len(ends) != 2:
        raise ValueError("Expected two enclosing endpoints for the first K+J eigenvalue")
    values["eigen.coarse_lower"] = fixed(ends[0][0], 14, ROUND_FLOOR)
    values["eigen.coarse_upper"] = fixed(ends[1][1], 14, ROUND_CEILING)
    cert = read_json("audit-numeric/certificates.json")
    values["xi.m4"] = cert["fourth_derivatives"]["xi"]
    values["gaussian.m4"] = cert["fourth_derivatives"]["gaussian"]
    values["dimension.asymptotic"] = cert["three_dimensional_asymptotic"]
    eigen = decimal_bounds(cert["minimum_eigenvalue"])
    values["eigen.refined"] = nearest(eigen, 18)
    gap = decimal_bounds(cert["dimension_gap"])
    exponent = gap[0].adjusted()
    coefficients = [value.scaleb(-exponent) for value in gap]
    values["gap.lower"] = scientific(fixed(coefficients[0], 5, ROUND_FLOOR), exponent)
    values["gap.upper"] = scientific(fixed(coefficients[1], 5, ROUND_CEILING), exponent)
    values["gap.approx"] = scientific(nearest(coefficients, 1), exponent)


def acoustic(values):
    rows = read_json("acoustic/window-results.json")["windows"]
    forward_by_role = Counter()
    for row in rows:
        prefix = f"audio.{row['start']}-{row['end']}."
        weights = row["weightings"]
        winners = []
        for weight in ("equalized", "native"):
            entry = weights[weight]
            errors = entry["mae"]
            winners.append(min(errors, key=errors.get))
            for predictor in ("zero", "forward", "reversed"):
                values[prefix + weight + "." + predictor] = fixed(errors[predictor], 5)
            if row["role"] == "reported" and weight == "equalized":
                for spacing, pairs in ((6, entry["odd_pairs"][:7]), (12, entry["odd_pairs"][7:])):
                    values[prefix + f"mean{spacing}"] = fixed(sum(pairs) / len(pairs), 5)
        if winners == ["forward", "forward"]:
            forward_by_role[row["role"]] += 1
        if (row["start"], row["end"]) == (54, 62):
            pairs = list(zip(weights["equalized"]["odd_pairs"], weights["native"]["odd_pairs"], strict=True))
            if not pairs or not all(a < 0 and b < 0 for a, b in pairs):
                raise ValueError("Both weightings must have negative odd correlation for every reversal pair")
            values["audio.negative_pairs"] = str(len(pairs))
    numbers = ["zero", "one", "two", "three", "four", "five", "six", "seven"]
    values["audio.intervening_wins"] = numbers[forward_by_role["post_hoc"]]
    values["audio.original_wins"] = "both" if forward_by_role["reported"] == 2 else numbers[forward_by_role["reported"]]
    comparison = read_json("acoustic/comparison.json")
    difference = comparison["max_absolute_difference"]
    exponent = difference.adjusted()
    values["audio.replay_bound"] = scientific(fixed(difference.scaleb(-exponent), 1, ROUND_CEILING), exponent)
    values["audio.replay_pairs"] = str(comparison["pair_comparisons"])


def independent_crosschecks(values):
    """Bind the primary outputs to separate, rerunnable Arb implementations."""
    base = ROOT / "independent-numeric"

    def compare(key, enclosure):
        digits = len(values[key].partition(".")[2])
        if nearest(arb_bounds(enclosure), digits) != values[key]:
            raise ValueError(f"Independent enclosure disagrees with printed {key}")

    def lines(name):
        return (base / name).read_text().splitlines()

    contrasts = {"plus": "sum", "minus": "diff"}
    fourier = dict(line.rsplit(" = ", 1) for line in lines("fourier-frozen.log"))
    for profile in ("xi", "Gaussian"):
        for operation, key in contrasts.items():
            compare(f"{profile.lower()}.{key}", fourier[f"a=8 distribution={profile} {operation}"])
    compare("xi.axis8", fourier["a=8 distribution=xi single"])
    compare("gaussian.variance", fourier["variance"])
    compare("lag.5.detailed", fourier["a=5 distribution=xi single"])

    # Preserve numeric labels when matching the frozen tables; row order has no meaning here.
    controls = lines("postcomparison-controls.log")
    caps = {}
    for text in controls:
        match = re.fullmatch(r"a = (\d+) three-event cap = (.+) H1 = (.+)", text)
        if match:
            caps[int(match[1])] = (match[2], match[3])
    h3 = dict(line.rsplit(" = ", 1) for line in lines("postcomparison-h3.log"))
    for a in (2, 4, 5, 8, 10):
        compare(f"lag.{a}.T", caps[a][0])
        compare(f"lag.{a}.H1", caps[a][1])
        compare(f"lag.{a}.H3", h3[f"a = {a} H3"])
    compare("xi.axis16", caps[16][1])
    scalar = dict(line.rsplit(" = ", 1) for line in controls)
    for key, label in (("lag.determinant", "a=5 three-event determinant"),
                       ("lag.excess", "a=5 excess of 0.7 over H1"),
                       ("gaussian.axis8", "Gaussian sum maximizer coordinate 1"),
                       ("gaussian.axis16", "Gaussian sum maximizer coordinate 2")):
        compare(key, scalar[label])


def claim_values():
    values = {}
    with localcontext() as ctx:
        ctx.prec = 144
        one_lag(values)
        joint(values)
        acoustic(values)
        independent_crosschecks(values)
    return values


def render(template, values):
    fields = Counter(FIELD.findall(template))
    missing = sorted(set(values) - fields.keys())
    unknown = sorted(fields.keys() - set(values))
    if missing or unknown:
        raise ValueError(f"Template field mismatch: missing {missing}, unknown {unknown}")
    # A correct number in the table must not conceal a missing binding in the abstract.
    for key, minimum in {"xi.sum": 3, "witness.value": 4}.items():
        if fields[key] < minimum:
            raise ValueError(f"Expected at least {minimum} bindings for {key}, got {fields[key]}")
    # Computational decimals in the body must be tracked even when the author adds a new paragraph.
    body = template.split("# References and provenance", 1)[0]
    literal = re.search(r"\d+\.\d{4,}", body)
    if literal:
        raise ValueError(f"Unbound numerical claim {literal.group()!r} in the manuscript template")
    result = FIELD.sub(lambda m: values[m[1]], template)
    if "{{claim:" in result:
        raise ValueError("Malformed claim field in manuscript template")
    return result


def check_text(expected, actual):
    if actual != expected:
        for number, (want, got) in enumerate(zip(expected.splitlines(), actual.splitlines()), 1):
            if want != got:
                break
        else:
            number = min(len(expected.splitlines()), len(actual.splitlines())) or 1
        raise ValueError(f"Deposited manuscript differs at line {number}. Edit the template, then run --write.")


def must_fail(label, function, *args):
    try:
        function(*args)
    except ValueError:
        print(f"PASS rejected {label}")
    else:
        raise ValueError(f"Regression: accepted {label}")


def mutation_tests(template, expected, values):
    # Replace one genuine occurrence at a time; every other appearance stays correct.
    for label, key in (("false lead sum", "xi.sum"), ("false witness coordinate", "witness.value"),
                       ("false eigenvalue lower endpoint", "eigen.coarse_lower"),
                       ("false eigenvalue upper endpoint", "eigen.coarse_upper"),
                       ("false dimension-gap bound", "gap.upper"),
                       ("false Gaussian table cell", "gaussian.diff"),
                       ("false reversal table cell", "audio.54-62.equalized.reversed")):
        old = values[key]
        mutated = expected.replace(old, "9" + old, 1)
        must_fail(label, check_text, expected, mutated)
    for key in ("xi.sum", "gap.lower", "audio.intervening_wins"):
        marker = "{{claim:" + key + "}}"
        must_fail("missing template field " + key, render, template.replace(marker, "", 1), values)
    must_fail("mismatched Xi source and independent Fourier result", independent_crosschecks,
              {**values, "xi.sum": "0.9123456789"})
    must_fail("mismatched Gaussian source and independent Fourier result", independent_crosschecks,
              {**values, "gaussian.diff": "0.7123456789"})
    must_fail("new unbound prose number", render, "The asserted ceiling is 0.912345.\n" + template, values)
    must_fail("ambiguous nearest rounding", nearest, (Decimal("0.12499"), Decimal("0.12501")), 2)
    if fixed(Decimal("0.12341"), 3, ROUND_FLOOR) != "0.123" or fixed(Decimal("0.12341"), 3, ROUND_CEILING) != "0.124":
        raise ValueError("Regression in outward interval formatting")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--check", action="store_true", help="check the printed manuscript (default)")
    action.add_argument("--write", action="store_true", help="regenerate the printed manuscript from its template")
    action.add_argument("--self-test", action="store_true", help="check the manuscript and run negative controls")
    args = parser.parse_args()
    template = SOURCE.read_bytes().decode("utf-8")
    values = claim_values()
    expected = render(template, values)
    if args.write:
        DEPOSIT.write_bytes(expected.encode("utf-8"))
    else:
        check_text(expected, DEPOSIT.read_bytes().decode("utf-8"))
    if args.self_test:
        mutation_tests(template, expected, values)
    print(f"PASS {len(FIELD.findall(template))} bindings to {len(values)} named values in the public manuscript")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, ArithmeticError) as error:
        sys.exit(f"FAIL {error}")
