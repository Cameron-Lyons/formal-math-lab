#!/usr/bin/env python3
"""Independent elementary-symmetric export audit; no solver or search."""

import hashlib
import json
import random
from collections import Counter
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
LABELS = ("T", "L", "M", "R")
PIVOTS = (0, 81, 90, 99)
EDGES = (("T", "M"), ("M", "L"), ("M", "R"))


def gf4_mul(a, b):
    # Polynomial-basis multiplication modulo X^2+X+1, independently of tables.
    result = 0
    for i in range(2):
        for j in range(2):
            if (a >> i) & (b >> j) & 1:
                result ^= 1 << (i + j)
    if result & 4:
        result ^= 7
    return result


def geometry():
    # Row r starts at r^2 and has length 2r+1. Each upper cell is one T apex.
    windows = [
        (r * r + j, (r + 1) ** 2 + j, (r + 1) ** 2 + j + 1, (r + 1) ** 2 + j + 2)
        for r in range(9)
        for j in range(2 * r + 1)
    ]
    roles = {label: {window[i] for window in windows} for i, label in enumerate(LABELS)}
    assert len(windows) == 81 and all(len(cells) == 81 for cells in roles.values())
    return windows, roles


def e2(cells):
    return set(combinations(sorted(cells), 2))


def linear_product(left, right):
    counts = Counter(tuple(sorted((i, j))) for i in left for j in right)
    return {term for term, n in counts.items() if n % 2}


def substitutions(roles):
    equations = [set(roles[label]) for label in LABELS]
    for i, pivot in enumerate(PIVOTS):
        source = next(j for j in range(i, 4) if pivot in equations[j])
        equations[i], equations[source] = equations[source], equations[i]
        for j in range(4):
            if j != i and pivot in equations[j]:
                equations[j] ^= equations[i]
    result = {p: equations[i] - {p} for i, p in enumerate(PIVOTS)}
    assert not any(set(PIVOTS) & rhs for rhs in result.values())
    for role in roles.values():
        remaining = set()
        for cell in role:
            remaining ^= result.get(cell, {cell})
        assert not remaining
    return result


def substitute(polynomial, replacements, free):
    index = {cell: i for i, cell in enumerate(free)}
    counts = Counter()
    for i, j in polynomial:
        for a in replacements.get(i, {i}):
            for b in replacements.get(j, {j}):
                counts[tuple(sorted((index[a], index[b])))] += 1
    return {term for term, n in counts.items() if n % 2}


def decode(encoded, variables, degrees=(2,)):
    if not isinstance(encoded, str) or not encoded.startswith("0x"):
        raise ValueError("invalid hex encoding")
    value = int(encoded, 16)
    if value < 0 or value >> (2 * variables):
        raise ValueError("packed monomial overflows variable count")
    factors = []
    for i in range(variables):
        exponent = value >> (2 * i) & 3
        if exponent == 3:
            raise ValueError("exponent 3 is not a reduced encoding")
        factors += [i] * exponent
    if len(factors) not in degrees:
        raise ValueError("unexpected ordinary degree")
    return tuple(factors)


def read_export(path, free, replacements):
    document = json.loads(path.read_text())
    assert document["format"] == "t-board-elementary-augmentation-v1"
    assert document["coefficient_field"] == "F2" and document["height"] == 10
    assert (
        document["variables"] == len(free) and document["free_original_cells"] == free
    )
    assert document["augmentation_only"] is True
    assert (
        document["required_base_moments"] == "retain the existing Fourier moment ideal"
    )
    assert document["pivot_substitutions"] == replacements
    source = HERE / "exact_parity_math_fourier_reduced.json"
    assert (
        document["reduced_base_source_sha256"]
        == hashlib.sha256(source.read_bytes()).hexdigest()
    )
    labels = ["elementary:e2:T"] + [f"elementary:e2:diff:{a}:{b}" for a, b in EDGES]
    assert [equation["label"] for equation in document["remaining_equations"]] == (
        labels + [label + ":frobenius" for label in labels]
    )
    assert document["generator_groups"] == {
        "elementary_quadratics": [0, 1, 2, 3],
        "frobenius_partners_modulo_cubics": [4, 5, 6, 7],
    }
    result = []
    for i, equation in enumerate(document["remaining_equations"]):
        decoded = [
            decode(term, len(free), (2,) if i < 4 else (1, 4))
            for term in equation["terms"]
        ]
        assert len(decoded) == len(set(decoded)), "duplicate semantic monomial"
        result.append(set(decoded))
    return result


def evaluate(polynomial, values):
    result = 0
    for term in polynomial:
        value = 1
        for i in term:
            value = gf4_mul(value, values[i])
        result ^= value
    return result


def partner(polynomial):
    # Square coefficients/variables, then use z^3=1. Ordinary exponents remain.
    result = set()
    for term in polynomial:
        factors = []
        for i, exponent in sorted(Counter(term).items()):
            factors += [i] * ((2 * exponent) % 3)
        result.add(tuple(factors))
    assert len(result) == len(polynomial)
    return result


def rank(rows):
    basis = {}
    for polynomial in rows:
        row = set(polynomial)
        while row:
            pivot = max(row)
            if pivot in basis:
                row ^= basis[pivot]
            else:
                basis[pivot] = row
                break
    return len(basis)


def histogram_checks():
    # Lucas's theorem computes binomial coefficients modulo2 directly;
    # independent of the generator's repeated linear-product recurrence.
    degrees = (1, 2, 4, 8, 16)
    powers = (1, 2, 3)
    terms = {
        degree: [
            (i, j, degree - i - j, powers[(j + 2 * (degree - i - j)) % 3])
            for i in range(degree + 1)
            for j in range(degree - i + 1)
        ]
        for degree in degrees
    }
    survivors = [0] * 5
    triples = 0
    for n0 in range(82):
        for n1 in range(82 - n0):
            n2 = 81 - n0 - n1
            values = []
            for degree in degrees:
                coefficient = 0
                for i, j, k, value in terms[degree]:
                    if i & ~n0 == 0 and j & ~n1 == 0 and k & ~n2 == 0:
                        coefficient ^= value
                values.append(coefficient)
            for stage, degree in enumerate(degrees):
                vanishing = not any(values[: stage + 1])
                congruent = all(
                    n % (2 * degree) == 27 % (2 * degree) for n in (n0, n1, n2)
                )
                assert vanishing == congruent, (n0, n1, n2, degree, values)
                survivors[stage] += vanishing
                if stage == 4 and vanishing:
                    assert (n0, n1, n2) == (27, 27, 27)
            triples += 1
    return {
        "histograms": triples,
        "degrees": list(degrees),
        "survivors": survivors,
        "method": "Lucas binomial parity and direct three-factor coefficient sum",
    }


def main():
    windows, roles = geometry()
    replacements = substitutions(roles)
    free = [cell for cell in range(100) if cell not in PIVOTS]
    raw = {label: e2(cells) for label, cells in roles.items()}
    optimized = [raw["T"]]
    for a, b in EDGES:
        sparse = e2(roles[a] - roles[b]) ^ e2(roles[b] - roles[a])
        correction = linear_product(roles[a] & roles[b], roles[a] ^ roles[b])
        assert raw[a] ^ raw[b] ^ sparse == correction
        assert correction, (
            "differences must not be assumed equal before unary reduction"
        )
        optimized.append(sparse)
    original_path = HERE / "exact_parity_math_elementary_original.json"
    reduced_path = HERE / "exact_parity_math_elementary_reduced.json"
    original = read_export(original_path, list(range(100)), {})
    reduced = read_export(
        reduced_path, free, {str(k): sorted(v) for k, v in replacements.items()}
    )
    assert original[:4] == optimized
    assert reduced[:4] == [substitute(p, replacements, free) for p in optimized]
    assert original[4:] == [partner(p) for p in original[:4]]
    assert reduced[4:] == [partner(p) for p in reduced[:4]]
    reduced_raw = {label: substitute(p, replacements, free) for label, p in raw.items()}
    assert reduced[0] == reduced_raw["T"]
    for i, (a, b) in enumerate(EDGES, 1):
        assert reduced[i] == reduced_raw[a] ^ reduced_raw[b]
    squares = [sum(i == j for i, j in polynomial) for polynomial in reduced[:4]]
    assert squares == [80, 32, 8, 8]
    old_quadratics = []
    for a, b in combinations(range(4), 2):
        counts = Counter(tuple(sorted((window[a], window[b]))) for window in windows)
        old = {term for term, n in counts.items() if n % 2}
        old_quadratics.append(substitute(old, replacements, free))
    assert rank(old_quadratics) == 6 and rank(old_quadratics + reduced[:4]) == 10
    rng = random.Random(0xE2A0D17)
    for _ in range(200):
        partial = [rng.randrange(4) for _ in free]
        full = [0] * 100
        for cell, value in zip(free, partial, strict=False):
            full[cell] = value
        for pivot, sources in replacements.items():
            for source in sources:
                full[pivot] ^= full[source]
        for before, after in zip(original[:4], reduced[:4], strict=False):
            assert evaluate(before, full) == evaluate(after, partial)
        # Partners are squares modulo domains, so compare on nonzero free
        # values separately; arbitrary-zero evaluation is not a domain test.
        nonzero = [rng.randrange(1, 4) for _ in free]
        for before, after in zip(reduced[:4], reduced[4:], strict=False):
            value = evaluate(before, nonzero)
            assert evaluate(after, nonzero) == gf4_mul(value, value)
    # Published complete boards and the uniform-triple invalid board.
    seeds = json.loads((HERE.parent / "sources/anc/certificates.json").read_text())[
        "ternary_seeds"
    ]
    gauge = json.loads((HERE / "exact_structure_gauge_certificate.json").read_text())[
        "boards"
    ]
    boards = {"".join(rows) for rows in seeds} | {item["flat"] for item in gauge[:24]}
    for board in boards:
        colors = list(map(int, board))
        assert len({tuple(colors[cell] for cell in w) for w in windows}) == 81
        values = [color + 1 for color in colors]
        assert all(
            Counter(colors[cell] for cell in role) == {0: 27, 1: 27, 2: 27}
            for role in roles.values()
        )
        assert all(evaluate(polynomial, values) == 0 for polynomial in original)
        assert all(
            evaluate(polynomial, [values[cell] for cell in free]) == 0
            for polynomial in reduced
        )
    invalid = "".join(
        json.loads((HERE / "exact_structure_counterexample.json").read_text())["rows"]
    )
    invalid_colors = list(map(int, invalid))
    assert len({tuple(invalid_colors[cell] for cell in w) for w in windows}) == 73
    assert all(evaluate(p, [c + 1 for c in invalid_colors]) == 0 for p in original)
    histograms = histogram_checks()
    assert histograms["histograms"] == 3403 and histograms["survivors"] == [
        820,
        190,
        55,
        10,
        1,
    ]
    malformed = ["0x0", "0x1", "0x3", hex(1 << (2 * 96)), hex(1 | (1 << 2) | (1 << 4))]
    for encoded in malformed:
        try:
            decode(encoded, 96)
        except ValueError:
            continue
        raise AssertionError("invalid degree/encoding accepted")
    report = {
        "status": "PASS",
        "original_terms": list(map(len, original)),
        "reduced_terms": list(map(len, reduced)),
        "ordinary_square_terms": squares,
        "old_quadratic_span_rank": 6,
        "augmented_quadratic_span_rank": 10,
        "partner_linear_term_counts": [
            sum(len(term) == 1 for term in p) for p in reduced[4:]
        ],
        "partner_quartic_term_counts": [
            sum(len(term) == 4 for term in p) for p in reduced[4:]
        ],
        "symbolic_role_difference_identities_checked": 3,
        "frobenius_partners_checked": 8,
        "all_four_substituted_polynomials_match": True,
        "free_variables": 96,
        "random_substitution_checks_including_zero": 200,
        "valid_boards_checked": len(boards),
        "uniform_triple_counterexample_passes_e2_but_remains_invalid": True,
        "histogram_checks": histograms,
        "invalid_encoding_cases_rejected": len(malformed),
        "full_count_status": "NOT_COMPUTED",
        "solver_runs": 0,
        "source_sha256": {
            str(p.name): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in (original_path, reduced_path)
        },
    }
    (HERE / "exact_elementary_review_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
