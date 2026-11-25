#!/usr/bin/env python3
"""Export and check the characteristic-two Fourier ideal; does not solve it."""

import json
import random
from collections import Counter
from itertools import product
from pathlib import Path

from exact_parity_math import toggle, windows

HERE = Path(__file__).resolve().parent
MUL = ((0, 0, 0, 0), (0, 1, 2, 3), (0, 2, 3, 1), (0, 3, 1, 2))
SQUARE = (0, 1, 3, 2)


def field_rank(rows):
    rows = [list(row) for row in rows]
    rank = 0
    for column in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = SQUARE[rows[rank][column]]
        rows[rank] = [MUL[inverse][x] for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][column]:
                scalar = rows[i][column]
                rows[i] = [
                    a ^ MUL[scalar][b]
                    for a, b in zip(rows[i], rows[rank], strict=False)
                ]
        rank += 1
    return rank


def packed_term(pairs):
    term = 0
    for cell, exponent in pairs:
        old = term >> (2 * cell) & 3
        new = (old + exponent) % 3
        term = (term & ~(3 << (2 * cell))) | (new << (2 * cell))
    return term


def unpack(term):
    pairs = []
    while term:
        bit = term & -term
        cell = (bit.bit_length() - 1) // 2
        exponent = term >> (2 * cell) & 3
        assert exponent in (1, 2)
        pairs.append((cell, exponent))
        term &= ~(3 << (2 * cell))
    return pairs


def evaluate(poly, values):
    out = 0
    for term in poly:
        value = 1
        for cell, exponent in unpack(term):
            value = MUL[value][values[cell] if exponent == 1 else SQUARE[values[cell]]]
        out ^= value
    return out


def original_equations():
    selected = []
    for exponents in product(range(3), repeat=4):
        if next((e for e in exponents if e), 0) != 1:
            continue
        poly = set()
        for window in windows(10):
            toggle(
                poly,
                packed_term(
                    (cell, e) for cell, e in zip(window, exponents, strict=False) if e
                ),
            )
        selected.append((exponents, poly))
    assert len(selected) == 40
    return selected


def eliminate(equations):
    pivots = [0, 81, 90, 99]
    rows = []
    for exponents, p in equations:
        if sum(exponents) == 1:
            rows.append(sum(1 << unpack(t)[0][0] for t in p))
    assert len(rows) == 4
    for i, cell in enumerate(pivots):
        j = next(j for j in range(i, 4) if rows[j] >> cell & 1)
        rows[i], rows[j] = rows[j], rows[i]
        for j in range(4):
            if j != i and rows[j] >> cell & 1:
                rows[j] ^= rows[i]
    substitutions = {}
    for cell, row in zip(pivots, rows, strict=False):
        row ^= 1 << cell
        assert all(not row >> pivot & 1 for pivot in pivots)
        substitutions[cell] = [v for v in range(100) if row >> v & 1]
    assert max(sum(cell in pivots for cell in w) for w in windows(10)) == 1
    free = [cell for cell in range(100) if cell not in pivots]
    index = {cell: i for i, cell in enumerate(free)}
    reduced = []
    for exponents, poly in equations:
        result = set()
        for term in poly:
            pairs = unpack(term)
            changed = [(cell, e) for cell, e in pairs if cell in pivots]
            fixed = [(index[cell], e) for cell, e in pairs if cell not in pivots]
            if not changed:
                toggle(result, packed_term(fixed))
            else:
                assert len(changed) == 1
                cell, e = changed[0]
                # (sum z)^2=sum z^2 in characteristic two.
                for replacement in substitutions[cell]:
                    toggle(result, packed_term([*fixed, (index[replacement], e)]))
        if sum(exponents) == 1:
            assert not result
        else:
            reduced.append(("moment:" + ",".join(map(str, exponents)), result))
    for cell in pivots:
        p = {0}  # L^3+1=L*L^2+1, reduced modulo free z_i^3+1.
        for a in substitutions[cell]:
            for b in substitutions[cell]:
                toggle(p, packed_term([(index[a], 1), (index[b], 2)]))
        reduced.append((f"pivot_domain:{cell}", p))
    return free, substitutions, reduced


def original_export(equations):
    document = {
        "format": "t-board-fourier-ideal-v1",
        "height": 10,
        "variables": 100,
        "coefficient_field": "F2; may extend scalars to F4 without changing vector-space dimension",
        "color_field": "F4=F2[w]/(w^2+w+1)",
        "colors": ["1", "w", "w^2"],
        "cell_index": "row^2+column, rows and columns zero-based",
        "domain_equations": [
            {"cell": cell, "polynomial": "z_cell^3+1"} for cell in range(100)
        ],
        "moment_equations": [
            {
                "role_exponents": list(e),
                "rhs": 0,
                "terms": [unpack(t) for t in sorted(p)],
            }
            for e, p in equations
        ],
        "status": "UNEVALUATED exact ideal; quotient dimension equals unrestricted board count",
    }
    (HERE / "exact_parity_math_fourier_original.json").write_text(
        json.dumps(document, indent=2) + "\n"
    )

    def singular_monomial(term):
        return (
            "*".join(
                f"z{cell}" + (f"^{e}" if e != 1 else "") for cell, e in unpack(term)
            )
            or "1"
        )

    lines = [
        "// Exact ideal only; no standard-basis computation is launched.",
        "// All coefficients lie in F2. The solution colors are roots in F4.",
        "ring R=2,(" + ",".join(f"z{i}" for i in range(100)) + "),dp;",
        "ideal I=",
    ]
    polynomials = [f"z{i}^3+1" for i in range(100)]
    polynomials += [
        "+".join(singular_monomial(t) for t in sorted(p)) for _, p in equations
    ]
    lines.append(",\n".join(polynomials) + ";")
    lines += [
        "// Future backend: compute a full standard basis, then count its",
        "// standard monomials using arbitrary-precision integer arithmetic.",
    ]
    (HERE / "exact_parity_math_fourier_original.sing").write_text(
        "\n".join(lines) + "\n"
    )


def main():
    equations = original_equations()
    original_export(equations)
    free, substitutions, reduced = eliminate(equations)
    document = {
        "format": "t-board-fourier-reduced-v1",
        "variables": 96,
        "coefficient_field": "F2",
        "free_original_cells": free,
        "free_domain_equations": "z_i^3+1 for all 96 free variables",
        "pivot_substitutions": substitutions,
        "monomial_encoding": "hex integer: exponent of free variable i in bits 2*i,2*i+1; exponents 0,1,2; coefficient1; constant=0x0",
        "remaining_equations": [
            {"label": label, "terms": [hex(t) for t in sorted(p)]}
            for label, p in reduced
        ],
        "status": "UNEVALUATED; includes36 moment equations and4 pivot-domain equations",
    }
    (HERE / "exact_parity_math_fourier_reduced.json").write_text(
        json.dumps(document, indent=2) + "\n"
    )

    # Invertibility of all81 Fourier coordinates on the81 possible patterns.
    matrix = []
    for exponents in product(range(3), repeat=4):
        row = []
        for values in product((1, 2, 3), repeat=4):
            value = 1
            for z, e in zip(values, exponents, strict=False):
                value = MUL[value][1 if e == 0 else z if e == 1 else SQUARE[z]]
            row.append(value)
        assert (0 if any(exponents) else 1) == __import__("functools").reduce(
            int.__xor__, row
        )
        matrix.append(row)
    assert field_rank(matrix) == 81

    # Existing independently validated boards, plus their reflections.
    certificate = json.loads(
        (HERE / "exact_structure_gauge_certificate.json").read_text()
    )
    boards = set()
    for entry in certificate["boards"]:
        flat = entry["flat"]
        boards.add(flat)
        boards.add("".join(flat[r * r : (r + 1) * (r + 1)][::-1] for r in range(10)))
    for flat in boards:
        values = [int(c) + 1 for c in flat]
        assert len({tuple(values[c] for c in w) for w in windows(10)}) == 81
        assert all(evaluate(p, values) == 0 for _, p in equations)
        partial = [values[c] for c in free]
        assert all(evaluate(p, partial) == 0 for _, p in reduced)
    # Check every exported equation under substituted random free assignments.
    rng = random.Random(0xF4F4)
    for _ in range(100):
        partial = [rng.choice((1, 2, 3)) for _ in free]
        values = [0] * 100
        for cell, value in zip(free, partial, strict=False):
            values[cell] = value
        for cell, sources in substitutions.items():
            for source in sources:
                values[cell] ^= values[source]
        for exponents, p in equations:
            if sum(exponents) == 1:
                assert evaluate(p, values) == 0
            else:
                label = "moment:" + ",".join(map(str, exponents))
                rp = next(poly for name, poly in reduced if name == label)
                assert evaluate(p, values) == evaluate(rp, partial)
            doubled = tuple(2 * e % 3 for e in exponents)
            conjugate = set()
            for w in windows(10):
                toggle(
                    conjugate,
                    packed_term(
                        (cell, e) for cell, e in zip(w, doubled, strict=False) if e
                    ),
                )
            assert evaluate(conjugate, values) == SQUARE[evaluate(p, values)]
        for cell in substitutions:
            p = next(poly for label, poly in reduced if label == f"pivot_domain:{cell}")
            assert evaluate(p, partial) == (MUL[values[cell]][SQUARE[values[cell]]] ^ 1)
    report = {
        "status": "PASS",
        "full_fourier_rank": 81,
        "selected_fourier_equations": 40,
        "original_equation_degree_histogram": dict(
            sorted(Counter(sum(e) for e, _ in equations).items())
        ),
        "original_moment_terms": sum(len(p) for _, p in equations),
        "original_domains": 100,
        "reduced_variables": 96,
        "reduced_free_domains": 96,
        "remaining_equations": len(reduced),
        "reduced_expanded_terms": sum(len(p) for _, p in reduced),
        "pivot_linear_terms": {cell: len(p) for cell, p in substitutions.items()},
        "valid_boards_checked": len(boards),
        "random_substitution_checks": 100,
        "full_count_status": "UNEVALUATED",
    }
    (HERE / "exact_parity_math_fourier_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
