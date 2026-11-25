#!/usr/bin/env python3
"""Export four redundant F2 quadratic elementary-symmetric constraints.

No ideal computation or board search. Arithmetic is ordinary polynomial
arithmetic: squared variables remain squared, not Boolean/idempotent.
"""

import argparse
import hashlib
import json
import random
from collections import Counter
from itertools import combinations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent
MUL = ((0, 0, 0, 0), (0, 1, 2, 3), (0, 2, 3, 1), (0, 3, 1, 2))
PIVOTS = [0, 81, 90, 99]
LABELS = ["T", "L", "M", "R"]


def toggle(poly, term):
    if term in poly:
        poly.remove(term)
    else:
        poly.add(term)


def pack(variables):
    counts = Counter(variables)
    assert all(e <= 2 for e in counts.values())
    return sum(e << (2 * v) for v, e in counts.items())


def unpack(term):
    pairs = []
    while term:
        v = ((term & -term).bit_length() - 1) // 2
        e = term >> (2 * v) & 3
        assert e in (1, 2)
        pairs.append((v, e))
        term &= ~(3 << (2 * v))
    return pairs


def geometry():
    cells = {(j - r, -r): r * r + j for r in range(10) for j in range(2 * r + 1)}
    windows = []
    for x, y in cells:
        positions = [(x, y + 1), (x - 1, y), (x, y), (x + 1, y)]
        if all(p in cells for p in positions):
            windows.append(tuple(cells[p] for p in positions))
    assert len(windows) == 81
    roles = {label: {w[i] for w in windows} for i, label in enumerate(LABELS)}
    assert all(len(role) == 81 for role in roles.values())
    return windows, roles


def derive_substitutions(roles):
    rows = [sum(1 << cell for cell in roles[label]) for label in LABELS]
    for i, cell in enumerate(PIVOTS):
        j = next(j for j in range(i, 4) if rows[j] >> cell & 1)
        rows[i], rows[j] = rows[j], rows[i]
        for j in range(4):
            if i != j and rows[j] >> cell & 1:
                rows[j] ^= rows[i]
    result = {}
    for cell, row in zip(PIVOTS, rows, strict=False):
        row ^= 1 << cell
        assert not any(row >> p & 1 for p in PIVOTS)
        result[cell] = [v for v in range(100) if row >> v & 1]
    return result


def e2(cells):
    return {pack(pair) for pair in combinations(sorted(cells), 2)}


def multiply_linear(a, b):
    result = set()
    for x in a:
        for y in b:
            toggle(result, pack((x, y)))
    return result


def substitute(poly, substitutions, free):
    indices = {cell: i for i, cell in enumerate(free)}
    result = set()
    for term in poly:
        factors = [cell for cell, exponent in unpack(term) for _ in range(exponent)]
        assert len(factors) == 2
        for a in substitutions.get(factors[0], [factors[0]]):
            for b in substitutions.get(factors[1], [factors[1]]):
                toggle(result, pack((indices[a], indices[b])))
    return result


def evaluate(poly, values):
    result = 0
    for term in poly:
        value = 1
        for cell, exponent in unpack(term):
            for _ in range(exponent):
                value = MUL[value][values[cell]]
        result ^= value
    return result


def frobenius(poly):
    """Square, then reduce only by ordinary free cubics z_i^3+1.

    An ordinary square monomial z_i^2 maps to z_i^4 == z_i, not to
    z_i^2 or1. Cross terms z_i*z_j map to z_i^2*z_j^2.
    """
    result = set()
    for term in poly:
        toggle(result, pack([v for v, e in unpack(term) for _ in range((2 * e) % 3)]))
    return result


def substitute_squared_quadratic(poly, substitutions, free):
    """Independently substitute a squared original quadratic modulo cubics."""
    indices = {cell: i for i, cell in enumerate(free)}
    result = set()
    for term in poly:
        factors = [cell for cell, exponent in unpack(term) for _ in range(exponent)]
        assert len(factors) == 2
        for a in substitutions.get(factors[0], [factors[0]]):
            for b in substitutions.get(factors[1], [factors[1]]):
                if a == b:
                    toggle(result, pack((indices[a],)))
                else:
                    toggle(
                        result, pack((indices[a], indices[a], indices[b], indices[b]))
                    )
    return result


def rank(polys):
    terms = sorted(set().union(*polys))
    columns = {term: i for i, term in enumerate(terms)}
    pivots = {}
    for poly in polys:
        row = sum(1 << columns[term] for term in poly)
        while row:
            pivot = row.bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
    return len(pivots)


def counts_check():
    stages = [1, 2, 4, 8, 16]
    survivors = [0] * 5
    total = 0
    for n0 in range(82):
        for n1 in range(82 - n0):
            counts = [n0, n1, 81 - n0 - n1]
            coeff = [1] + [0] * 16
            for color, multiplicity in zip((1, 2, 3), counts, strict=False):
                for _ in range(multiplicity):
                    for d in range(16, 0, -1):
                        coeff[d] ^= MUL[color][coeff[d - 1]]
            for i, degree in enumerate(stages):
                vanished = all(coeff[d] == 0 for d in stages[: i + 1])
                modulus = 2 * degree
                congruent = all(n % modulus == 27 % modulus for n in counts)
                assert vanished == congruent
                survivors[i] += int(vanished)
            total += 1
    assert total == 3403 and survivors == [820, 190, 55, 10, 1]
    return {
        "count_triples": total,
        "successive_degrees": stages,
        "successive_moduli": [2, 4, 8, 16, 32],
        "successive_residues": [1, 3, 3, 11, 27],
        "successive_survivors": survivors,
        "sole_final_count_triple": [27, 27, 27],
    }


def build():
    windows, roles = geometry()
    substitutions = derive_substitutions(roles)
    free = [cell for cell in range(100) if cell not in PIVOTS]
    source_path = HERE / "exact_parity_math_fourier_reduced.json"
    source_bytes = source_path.read_bytes()
    source = json.loads(source_bytes)
    assert source["free_original_cells"] == free
    assert source["pivot_substitutions"] == {
        str(k): v for k, v in substitutions.items()
    }

    # A spanning tree with minimum edge weight among the six role differences:
    # edge cost 2*C(81-|intersection|,2). T has three272 edges; LM,MR cost72.
    raw = {label: e2(cells) for label, cells in roles.items()}
    equations = [("elementary:e2:T", raw["T"])]
    differences = []
    for a, b in [("T", "M"), ("M", "L"), ("M", "R")]:
        poly = e2(roles[a] - roles[b]) ^ e2(roles[b] - roles[a])
        # Exact ordinary-ring identity; no domain or Boolean reduction used.
        correction = multiply_linear(roles[a] & roles[b], roles[a] ^ roles[b])
        assert raw[a] ^ raw[b] ^ poly == correction
        equations.append((f"elementary:e2:diff:{a}:{b}", poly))
        differences.append(
            {
                "roles": [a, b],
                "exclusive_set_sizes": [
                    len(roles[a] - roles[b]),
                    len(roles[b] - roles[a]),
                ],
                "terms": len(poly),
            }
        )
    reduced = [(label, substitute(p, substitutions, free)) for label, p in equations]
    reduced_raw = {
        label: substitute(p, substitutions, free) for label, p in raw.items()
    }
    assert reduced[0][1] == reduced_raw["T"]
    for (a, b), (_, p) in zip(
        [("T", "M"), ("M", "L"), ("M", "R")], reduced[1:], strict=False
    ):
        assert p == reduced_raw[a] ^ reduced_raw[b]
    assert rank(list(reduced_raw.values())) == rank([p for _, p in reduced]) == 4

    old_quadratics = []
    for i, j in combinations(range(4), 2):
        poly = set()
        for window in windows:
            toggle(poly, pack((window[i], window[j])))
        old_quadratics.append(substitute(poly, substitutions, free))
    actual_low_degree = []
    for equation in source["remaining_equations"]:
        p = {int(term, 16) for term in equation["terms"]}
        degree = max((sum(e for _, e in unpack(t)) for t in p), default=-1)
        if degree <= 2:
            actual_low_degree.append(p)
    assert {frozenset(p) for p in actual_low_degree} == {
        frozenset(p) for p in old_quadratics
    }
    assert len(actual_low_degree) == 6
    old_rank = rank(old_quadratics)
    augmented_rank = rank(old_quadratics + [p for _, p in reduced])
    assert old_rank == 6 and augmented_rank == 10

    original_partners = [(label + ":frobenius", frobenius(p)) for label, p in equations]
    reduced_partners = [(label + ":frobenius", frobenius(p)) for label, p in reduced]
    for (_, p), (_, rp), (_, partner) in zip(
        equations, reduced, reduced_partners, strict=False
    ):
        assert partner == substitute_squared_quadratic(p, substitutions, free)
        assert frobenius(partner) == rp

    # Independent evaluations include zero free values: the substitution
    # identities hold as ordinary polynomials, without imposing cubic domains.
    rng = random.Random(0xE2E2)
    for _ in range(100):
        partial = [rng.randrange(4) for _ in free]
        full = [0] * 100
        for cell, value in zip(free, partial, strict=False):
            full[cell] = value
        for cell, sources in substitutions.items():
            for other in sources:
                full[cell] ^= full[other]
        for (_, p), (_, rp) in zip(equations, reduced, strict=False):
            assert evaluate(p, full) == evaluate(rp, partial)
        for (_, rp), (_, partner) in zip(reduced, reduced_partners, strict=False):
            value = evaluate(rp, partial)
            assert evaluate(partner, partial) == MUL[value][value]

    certificates = json.loads(
        (HERE / "exact_structure_gauge_certificate.json").read_text()
    )
    board_count = 0
    for entry in certificates["boards"]:
        full = [int(c) + 1 for c in entry["flat"]]
        assert {tuple(full[c] for c in w) for w in windows} == set(
            product((1, 2, 3), repeat=4)
        )
        for cells in roles.values():
            assert Counter(full[c] for c in cells) == {1: 27, 2: 27, 3: 27}
        assert all(evaluate(p, full) == 0 for _, p in equations)
        partial = [full[c] for c in free]
        assert all(evaluate(p, partial) == 0 for _, p in reduced)
        assert all(evaluate(p, partial) == 0 for _, p in reduced_partners)
        board_count += 1

    def export(eqs, cells, reduced_model):
        return {
            "format": "t-board-elementary-augmentation-v1",
            "height": 10,
            "coefficient_field": "F2",
            "variables": len(cells),
            "free_original_cells": cells,
            "scope": "unrestricted ternary boards; redundant generators only",
            "augmentation_only": True,
            "required_base_domains": (
                "retain96 ordinary free cubics and4 substituted pivot-domain equations"
                if reduced_model
                else "retain all100 ordinary z_i^3+1 equations"
            ),
            "required_base_moments": "retain the existing Fourier moment ideal",
            "generator_groups": {
                "elementary_quadratics": [0, 1, 2, 3],
                "frobenius_partners_modulo_cubics": [4, 5, 6, 7],
            },
            "frobenius_rule": "double each exponent modulo3; ordinary square z_i^2 maps to linear z_i; retain all free cubics",
            "monomial_encoding": "hex integer: exponent of variable i in bits2*i,2*i+1; coefficient1; exponent2 is an ordinary square",
            "pivot_substitutions": (
                {str(k): v for k, v in substitutions.items()} if reduced_model else {}
            ),
            "reduced_base_source_sha256": hashlib.sha256(source_bytes).hexdigest(),
            "remaining_equations": [
                {"label": label, "terms": [hex(t) for t in sorted(p)]}
                for label, p in eqs
            ],
            "full_count_status": "UNEVALUATED",
        }

    original_document = export(equations + original_partners, list(range(100)), False)
    reduced_document = export(reduced + reduced_partners, free, True)
    audit = {
        "status": "PASS",
        "count_congruence_exhaustive": counts_check(),
        "role_intersection_matrix": [
            [len(roles[a] & roles[b]) for b in LABELS] for a in LABELS
        ],
        "role_labels": LABELS,
        "role_cell_lists": {k: sorted(v) for k, v in roles.items()},
        "raw_role_e2_term_counts": {k: len(v) for k, v in raw.items()},
        "optimized_differences": differences,
        "original_equation_terms": {label: len(p) for label, p in equations},
        "reduced_equation_terms": {label: len(p) for label, p in reduced},
        "reduced_square_terms": {
            label: sum(any(e == 2 for _, e in unpack(t)) for t in p)
            for label, p in reduced
        },
        "all_primary_equation_terms_ordinary_degree2": all(
            sum(e for _, e in unpack(t)) == 2 for _, p in equations + reduced for t in p
        ),
        "original_frobenius_terms": {label: len(p) for label, p in original_partners},
        "reduced_frobenius_degree_histograms": {
            label: {
                str(d): n
                for d, n in sorted(
                    Counter(sum(e for _, e in unpack(t)) for t in p).items()
                )
            }
            for label, p in reduced_partners
        },
        "frobenius_substitution_independently_matches": True,
        "new_equations_rank_after_elimination": 4,
        "existing_quadratic_moment_rank_after_elimination": old_rank,
        "existing_degree_at_most2_generator_count": len(actual_low_degree),
        "augmented_quadratic_polynomial_span_rank": augmented_rank,
        "random_substitution_checks_including_zero": 100,
        "existing_valid_boards_checked": board_count,
        "substitutions_match_existing_reduced_source": True,
        "full_count_status": "UNEVALUATED; no solver run",
    }
    return original_document, reduced_document, audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    documents = build()
    for suffix, document in zip(
        ("original", "reduced", "audit"), documents, strict=False
    ):
        path = HERE / f"exact_parity_math_elementary_{suffix}.json"
        if args.check:
            assert json.loads(path.read_text()) == document
        else:
            path.write_text(json.dumps(document, indent=2) + "\n")
    print(
        json.dumps(
            {
                key: value
                for key, value in documents[-1].items()
                if key != "role_cell_lists"
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
