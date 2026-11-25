#!/usr/bin/env python3
"""Exact ANF/moment linear algebra for T-board parity constraints (stdlib only)."""

import json
import time
from collections import Counter
from itertools import combinations, product
from pathlib import Path


def windows(h):
    return [
        ((r - 1) ** 2 + j, r * r + j, r * r + j + 1, r * r + j + 2)
        for r in range(1, h)
        for j in range(2 * r - 1)
    ]


def toggle(target, item):
    if item in target:
        target.remove(item)
    else:
        target.add(item)


def monomial(variables):
    out = 0
    for v in variables:
        out |= 1 << v
    return out


def moments(h, colors):
    """Role labels -1=constant, 0..colors-2=explicit color indicator."""
    out = []
    for labels in product(range(-1, colors - 1), repeat=4):
        selected = [(role, color) for role, color in enumerate(labels) if color >= 0]
        if not selected:
            continue
        # Uniform complete pattern coverage: omitted-role sum is colors^(4-k).
        p = {0} if colors ** (4 - len(selected)) % 2 else set()
        for window in windows(h):
            term = monomial(
                (colors - 1) * window[role] + color for role, color in selected
            )
            toggle(p, term)
        out.append((labels, p))
    return out


def multiply_variable(p, variable, colors):
    out = set()
    bit = 1 << variable
    for term in p:
        term |= bit  # Boolean variables are idempotent.
        if colors == 3 and (term & (term >> 1) & SUM_EVEN_BITS):
            continue  # Two explicit colors at the same cell cannot coexist.
        toggle(out, term)
    return out


SUM_EVEN_BITS = sum(1 << i for i in range(0, 200, 2))


def gf2_echelon(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
    return pivots


def rank_polynomials(polynomials):
    monomials = sorted(set().union(*polynomials), key=lambda x: (x.bit_count(), x))
    index = {term: i for i, term in enumerate(monomials)}
    rows = [sum(1 << index[term] for term in p) for p in polynomials]
    return len(gf2_echelon(rows))


def linear_and_quadratic_analysis(h, colors):
    started = time.monotonic()
    variables = (colors - 1) * h * h
    polys = moments(h, colors)
    by_degree = {}
    for degree in range(1, 5):
        by_degree[degree] = [
            p for labels, p in polys if sum(label >= 0 for label in labels) == degree
        ]
    linear = by_degree[1]
    quadratic = by_degree[2]
    generated = linear + [
        multiply_variable(p, v, colors) for p in linear for v in range(variables)
    ]
    terms = [0] + [1 << v for v in range(variables)]
    terms += [
        monomial((a, b))
        for a, b in combinations(range(variables), 2)
        if not (colors == 3 and a // 2 == b // 2)
    ]
    indices = {term: i for i, term in enumerate(terms)}

    def encode(p):
        return sum(1 << indices[term] for term in p)

    before = gf2_echelon(map(encode, generated))
    after = gf2_echelon(map(encode, generated + quadratic))
    linear_rows = [row for pivot, row in after.items() if pivot <= variables]
    linear_rank = len(gf2_echelon(linear_rows))
    assert all(pivot != 0 for pivot in gf2_echelon(linear_rows))
    return {
        "height": h,
        "colors": colors,
        "variables": variables,
        "moment_equations": len(polys),
        "degree_counts": {degree: len(ps) for degree, ps in by_degree.items()},
        "degree_polynomial_ranks": {
            degree: rank_polynomials(ps) for degree, ps in by_degree.items()
        },
        "degree_two_quotient_columns": len(terms),
        "linear_and_variable_multiple_rank": len(before),
        "with_quadratic_moments_rank": len(after),
        "new_quadratic_conditions_mod_linear_ideal": len(after) - len(before),
        "all_degree_two_linear_consequence_rank": linear_rank,
        "seconds": time.monotonic() - started,
    }


def tensor_basis_check():
    patterns = list(product(range(3), repeat=4))
    labels = list(product(range(-1, 2), repeat=4))
    rows = []
    for label in labels:
        mask = 0
        for i, pattern in enumerate(patterns):
            if all(a < 0 or a == b for a, b in zip(label, pattern, strict=False)):
                mask |= 1 << i
        assert mask.bit_count() % 2 == 1
        rows.append(mask)
    assert len(gf2_echelon(rows)) == 81
    return {"moment_transform_rank": 81, "all_row_sums_odd": True}


def boundary_elimination(h, colors):
    variables = (colors - 1) * h * h
    pivot_cells = [0, (h - 1) ** 2, (h - 1) ** 2 + h - 1, h * h - 1]
    pivot_variables = [
        (colors - 1) * cell + c for cell in pivot_cells for c in range(colors - 1)
    ]
    polys = moments(h, colors)
    linear = [p for labels, p in polys if sum(x >= 0 for x in labels) == 1]
    rows = []
    for p in linear:
        row = 0
        for term in p:
            row ^= (1 << variables) if term == 0 else term
        rows.append(row)
    for i, variable in enumerate(pivot_variables):
        j = next(j for j in range(i, len(rows)) if rows[j] >> variable & 1)
        rows[i], rows[j] = rows[j], rows[i]
        for j in range(len(rows)):
            if j != i and rows[j] >> variable & 1:
                rows[j] ^= rows[i]
    substitutions = {}
    for variable, row in zip(pivot_variables, rows, strict=False):
        row ^= 1 << variable
        assert not any(row >> v & 1 for v in pivot_variables)
        p = {1 << v for v in range(variables) if row >> v & 1}
        if row >> variables & 1:
            p.add(0)
        substitutions[variable] = p
    assert max(sum(cell in pivot_cells for cell in w) for w in windows(h)) == 1

    def multiply(a, b):
        out = set()
        for x in a:
            for y in b:
                term = x | y
                if colors == 3 and term & (term >> 1) & SUM_EVEN_BITS:
                    continue
                toggle(out, term)
        return out

    def substitute(p):
        out = set()
        for term in p:
            expanded = {0}
            while term:
                bit = term & -term
                term ^= bit
                v = bit.bit_length() - 1
                expanded = multiply(expanded, substitutions.get(v, {bit}))
            out.symmetric_difference_update(expanded)
        return out

    equations = []
    for labels, p in polys:
        transformed = substitute(p)
        if sum(x >= 0 for x in labels) == 1:
            assert not transformed
        else:
            equations.append(("moment:" + ",".join(map(str, labels)), transformed))
    if colors == 3:
        for cell in range(h * h):
            if cell in pivot_cells:
                p = multiply(substitutions[2 * cell], substitutions[2 * cell + 1])
            else:
                # Keep explicit free-cell exclusion generators; reductions
                # above used these relations and preserve the same ideal.
                p = {monomial((2 * cell, 2 * cell + 1))}
            equations.append((f"cell:{cell}", p))
    free = [v for v in range(variables) if v not in pivot_variables]
    compressed = {old: new for new, old in enumerate(free)}

    def compress(term):
        out = 0
        while term:
            bit = term & -term
            term ^= bit
            out |= 1 << compressed[bit.bit_length() - 1]
        return out

    exported = {
        "height": h,
        "colors": colors,
        "variables": len(free),
        "original_free_variables": free,
        "pivot_cells": pivot_cells,
        "pivot_substitutions": {
            str(v): [hex(compress(t)) for t in sorted(p)]
            for v, p in substitutions.items()
        },
        "equations": [
            {"label": label, "terms": [hex(compress(t)) for t in sorted(p)]}
            for label, p in equations
        ],
    }
    path = Path(__file__).with_name(f"exact_parity_math_reduced_{colors}.json")
    path.write_text(json.dumps(exported, indent=2) + "\n")
    if colors == 2:
        lines = [
            f"{len(free)} {len(equations)}",
            " ".join(map(str, free)),
            str(len(substitutions)),
        ]
        for v, p in substitutions.items():
            mask = 0
            for t in p:
                if t:
                    mask |= compress(t)
            lines.append(f"{v} {mask:x} {int(0 in p)}")
        for _, p in equations:
            lines.append(
                str(len(p)) + " " + " ".join(f"{compress(t):x}" for t in sorted(p))
            )
        path.with_suffix(".dat").write_text("\n".join(lines) + "\n")
    return {
        "pivot_cells": pivot_cells,
        "remaining_variables": len(free),
        "pivot_affine_term_counts": {v: len(p) for v, p in substitutions.items()},
        "equations": len(equations),
        "equation_degree_histogram": dict(
            sorted(Counter(max(map(int.bit_count, p)) for _, p in equations).items())
        ),
        "total_terms": sum(len(p) for _, p in equations),
        "largest_equation_terms": max(len(p) for _, p in equations),
        "export_file": path.name,
    }


def main():
    result = {
        "basis": tensor_basis_check(),
        "ternary": linear_and_quadratic_analysis(10, 3),
        "binary": linear_and_quadratic_analysis(5, 2),
        "ternary_elimination": boundary_elimination(10, 3),
        "binary_elimination": boundary_elimination(5, 2),
    }
    path = Path(__file__).with_name("exact_parity_math_results.json")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
