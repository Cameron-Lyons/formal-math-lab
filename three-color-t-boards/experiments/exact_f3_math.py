#!/usr/bin/env python3
"""Exact natural-F3 prefix model; export and audit only, never run a solver."""

import argparse
import hashlib
import json
import random
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
GRAY = [
    "1001",
    "1000",
    "1010",
    "1011",
    "1111",
    "1110",
    "1100",
    "0100",
    "0110",
    "0111",
    "0011",
    "0001",
]
PIVOTS = [80, 16, 81, 99]


def add_into(target, source, scale=1):
    for term, coefficient in source.items():
        value = (target.get(term, 0) + scale * coefficient) % 3
        if value:
            target[term] = value
        elif term in target:
            del target[term]


def geometry():
    cells = {(j - r, -r): r * r + j for r in range(10) for j in range(2 * r + 1)}
    windows = []
    for x, y in cells:
        points = [(x, y + 1), (x - 1, y), (x, y), (x + 1, y)]
        if all(p in cells for p in points):
            windows.append(tuple(cells[p] for p in points))
    assert len(windows) == 81
    roles = [{w[i] for w in windows} for i in range(4)]
    assert all(len(s) == 81 for s in roles)
    signatures = {c: "".join(str(int(c in role)) for role in roles) for c in range(100)}
    assert set(signatures.values()) == set(GRAY)
    order = sorted(range(100), key=lambda c: (GRAY.index(signatures[c]), c))
    return windows, roles, order


def coordinates(roles, order):
    initial = {}
    for position, cell in enumerate(order):
        initial[cell] = {position: 1}
        if position:
            initial[cell][position - 1] = 2
    unary = []
    for role in roles:
        poly = {}
        for c in role:
            add_into(poly, initial[c])
        unary.append(poly)
    rows = [p.copy() for p in unary]
    for i, pivot in enumerate(PIVOTS):
        j = next(j for j in range(i, 4) if rows[j].get(pivot, 0))
        rows[i], rows[j] = rows[j], rows[i]
        inverse = rows[i][pivot]  # 1^-1=1, 2^-1=2 in F3
        rows[i] = {v: c * inverse % 3 for v, c in rows[i].items()}
        for j in range(4):
            if i != j and rows[j].get(pivot, 0):
                add_into(rows[j], rows[i], -rows[j][pivot])
    replacements = {}
    for pivot, row in zip(PIVOTS, rows, strict=False):
        assert row[pivot] == 1
        replacements[pivot] = {v: -c % 3 for v, c in row.items() if v != pivot}
        assert not set(replacements[pivot]) & set(PIVOTS)
    assert replacements == {
        80: {},
        16: {97: 1},
        81: {8: 2, 72: 1, 98: 1},
        99: {7: 2, 9: 1, 65: 2, 82: 1},
    }
    free = [v for v in range(100) if v not in PIVOTS]
    index = {v: i for i, v in enumerate(free)}
    prefix_forms = {v: replacements.get(v, {v: 1}) for v in range(100)}
    forms = {}
    for cell, linear in initial.items():
        expanded = {}
        for v, c in linear.items():
            add_into(expanded, prefix_forms[v], c)
        forms[cell] = {index[v]: c for v, c in expanded.items()}
    # Exact linear inverse, not just evaluations: cumulative original colors
    # reconstruct each free prefix and each solved pivot prefix.
    accumulated = {}
    for position, cell in enumerate(order):
        add_into(accumulated, forms[cell])
        expected = {index[v]: c for v, c in prefix_forms[position].items()}
        assert accumulated == expected
    for role in roles:
        check = {}
        for cell in role:
            add_into(check, forms[cell])
        assert not check
    return unary, replacements, free, forms


@lru_cache(maxsize=300000)
def field_reduce(word):
    """Ordinary reduction modulo y_i^3-y_i, including y_i=0.

    A positive exponent n maps to 1+((n-1)%2), never to0.
    """
    out = 0
    while word:
        v = ((word & -word).bit_length() - 1) // 4
        e = word >> (4 * v) & 15
        out |= (1 + (e - 1) % 2) << (4 * v)
        word &= ~(15 << (4 * v))
    return out


def multiply(a, b):
    out = {}
    for x, c in a.items():
        for y, d in b.items():
            t = field_reduce(x + y)
            value = (out.get(t, 0) + c * d) % 3
            if value:
                out[t] = value
            elif t in out:
                del out[t]
    return out


def unpack(word):
    pairs = []
    while word:
        v = ((word & -word).bit_length() - 1) // 4
        e = word >> (4 * v) & 15
        pairs.append((v, e))
        word &= ~(15 << (4 * v))
    return pairs


def evaluate(poly, values):
    out = 0
    for t, c in poly.items():
        value = c
        for v, e in unpack(t):
            value = value * pow(values[v], e, 3) % 3
        out = (out + value) % 3
    return out


def field_rank(matrix):
    a = [row[:] for row in matrix]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][col] % 3), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = a[rank][col] % 3
        a[rank] = [inv * v % 3 for v in a[rank]]
        for i in range(len(a)):
            if i != rank and a[i][col] % 3:
                scale = a[i][col] % 3
                a[i] = [
                    (x - scale * y) % 3 for x, y in zip(a[i], a[rank], strict=False)
                ]
        rank += 1
        if rank == len(a):
            break
    return rank


def moment_polynomials(windows, forms):
    powers = {}
    for cell, linear in forms.items():
        p = {1 << (4 * v): c for v, c in linear.items()}
        powers[cell] = [{0: 1}, p, multiply(p, p)]
    moments = []
    eliminated = []
    for exponents in product(range(3), repeat=4):
        if not any(exponents):
            continue
        target = int(exponents == (2, 2, 2, 2))
        poly = {0: 2} if target else {}
        for window in windows:
            p = {0: 1}
            for cell, e in zip(window, exponents, strict=False):
                if e:
                    p = multiply(p, powers[cell][e])
            add_into(poly, p)
        if not poly:
            eliminated.append(exponents)
        else:
            moments.append((exponents, target, poly))
    assert len(eliminated) == 4 and all(sum(e) == 1 for e in eliminated)
    assert len(moments) == 76
    assert sum(sum(e) == 2 and max(e) == 2 for e, _, _ in moments) == 4
    return moments, eliminated


def validate(windows, order, free, forms, moments, replacements):
    exponents = list(product(range(3), repeat=4))
    patterns = list(product(range(3), repeat=4))
    transform = []
    for e in exponents:
        row = []
        for pattern in patterns:
            v = 1
            for c, power in zip(pattern, e, strict=False):
                v = v * pow(c, power, 3) % 3
            row.append(v)
        assert sum(row) % 3 == int(e == (2, 2, 2, 2))
        transform.append(row)
    assert field_rank(transform) == 81
    # Indicator formula, including the convention z^0=1 at z=0.
    for c in range(3):
        for z in range(3):
            assert (1 - (z - c) ** 2) % 3 == int(z == c)

    rng = random.Random(0xF300)
    for _ in range(12):
        y = [rng.randrange(3) for _ in free]
        z = {cell: sum(c * y[v] for v, c in f.items()) % 3 for cell, f in forms.items()}
        cumulative = []
        s = 0
        for cell in order:
            s = (s + z[cell]) % 3
            cumulative.append(s)
        assert [cumulative[v] for v in free] == y
        for pivot, linear in replacements.items():
            assert (
                cumulative[pivot]
                == sum(c * cumulative[v] for v, c in linear.items()) % 3
            )
        for e, target, poly in moments:
            direct = 0
            for w in windows:
                value = 1
                for cell, power in zip(w, e, strict=False):
                    value = value * pow(z[cell], power, 3) % 3
                direct = (direct + value) % 3
            assert evaluate(poly, y) == (direct - target) % 3
    fixtures = json.loads(
        (HERE / "exact_structure_gauge_certificate.json").read_text()
    )["boards"]
    for entry in fixtures:
        z = list(map(int, entry["flat"]))
        assert {tuple(z[c] for c in w) for w in windows} == set(patterns)
        cumulative = []
        s = 0
        for cell in order:
            s = (s + z[cell]) % 3
            cumulative.append(s)
        y = [cumulative[v] for v in free]
        assert all(
            sum(c * y[v] for v, c in forms[cell].items()) % 3 == z[cell]
            for cell in range(100)
        )
        assert all(evaluate(poly, y) == 0 for _, _, poly in moments)
    return {
        "tensor_moment_rank": 81,
        "color_indicator_identity_checked": True,
        "random_free_assignments_checked": 12,
        "existing_valid_boards_checked": len(fixtures),
        "linear_forward_inverse_symbolically_checked": True,
    }


def polynomial_record(label, poly):
    return {"label": label, "terms": [[c, hex(t)] for t, c in sorted(poly.items())]}


def expression(poly):
    summands = []
    for word, coefficient in sorted(poly.items()):
        factors = [str(coefficient)] if coefficient != 1 or word == 0 else []
        factors.extend(
            f"x{v + 1}" + (f"^{e}" if e != 1 else "") for v, e in unpack(word)
        )
        summands.append("*".join(factors))
    return "+".join(summands) or "0"


def build():
    windows, roles, order = geometry()
    unary, replacements, free, forms = coordinates(roles, order)
    frozen_prefix = json.loads(
        (HERE / "exact_msolve_elementary_analysis_prefix_gray_model.json").read_text()
    )
    assert (
        order == frozen_prefix["original_cell_order"]
        and free == frozen_prefix["free_prefix_variables"]
    )
    moments, eliminated = moment_polynomials(windows, forms)
    checks = validate(windows, order, free, forms, moments, replacements)
    domains = [{3 << (4 * i): 1, 1 << (4 * i): 2} for i in range(96)]
    document = {
        "format": "t-board-natural-f3-prefix-v1",
        "variables": 96,
        "height": 10,
        "coefficient_characteristic": 3,
        "coefficient_field": "F3",
        "ring_type": "ordinary polynomial ring",
        "color_values": [0, 1, 2],
        "extension_variable": False,
        "scope": "full labeled ternary boards",
        "prefix": "",
        "fixed_original_cells": [],
        "symmetry_normalization": False,
        "count_divisor": 1,
        "count_multiplier": 1,
        "original_cell_order": order,
        "signature_group_order": GRAY,
        "forward_map": "y_j=sum_(k<=j) z_order[k] overF3",
        "inverse_map": "z_order[j]=y_j-y_(j-1), y_(-1)=0",
        "unary_equations_before_elimination": [
            {str(v): c for v, c in sorted(p.items())} for p in unary
        ],
        "eliminated_prefix_variables": PIVOTS,
        "prefix_variable_substitutions": {
            str(v): {str(j): c for j, c in sorted(p.items())}
            for v, p in replacements.items()
        },
        "free_prefix_variables": free,
        "original_color_linear_forms": {
            str(c): {str(v): a for v, a in sorted(f.items())}
            for c, f in sorted(forms.items())
        },
        "linear_form_indices": "compressed free-prefix indices0..95; substitution indices are original prefix indices0..99",
        "monomial_encoding": "hex integer: ordinary exponent of free variable i in bits4*i..4*i+3",
        "term_encoding": "[coefficient,hex_monomial], coefficient1 or2 modulo3; terms are the full polynomial set equal to zero",
        "moment_reduction": "reduced only by retained y_i^3-y_i; positive exponent n becomes1+((n-1)%2), never0",
        "domain_equations": [
            polynomial_record(f"field:{i}", p) for i, p in enumerate(domains)
        ],
        "moment_equations": [
            dict(
                polynomial_record("moment:" + ",".join(map(str, e)), p),
                original_role_exponents=list(e),
                target_moment=target,
                target_already_subtracted=True,
            )
            for e, target, p in moments
        ],
        "original_nonconstant_moments": 80,
        "eliminated_linear_moments": [list(e) for e in eliminated],
        "retained_moments": 76,
        "generators": 172,
        "pivot_domain_equations": 0,
        "constant_moment": "81=0 inF3; automatic",
        "nonzero_moment_target": "M_(2,2,2,2)=1; all other moments target0",
        "extra_histogram_equations": False,
        "status": "PREPARED_NOT_RUN",
        "standard_basis_complete": False,
        "full_count_status": "UNEVALUATED",
    }
    encoded = json.dumps(document, indent=2) + "\n"
    text = ",".join(f"x{i + 1}" for i in range(96)) + "\n3\n"
    text += (
        ",\n".join(expression(p) for p in domains + [p for _, _, p in moments]) + "\n"
    )
    audit = {
        "status": "PASS",
        "scope": "exact unrestricted natural-F3 model; no solver run",
        "variables": 96,
        "coefficient_characteristic": 3,
        "generators": 172,
        "field_domain_equations": 96,
        "field_domain_terms": 192,
        "pivot_domains_needed": 0,
        "retained_moments": 76,
        "retained_unary_quadratic_moments": 4,
        "moment_terms": sum(len(p) for _, _, p in moments),
        "moment_term_count_by_exponents": {
            ",".join(map(str, e)): len(p) for e, _, p in moments
        },
        "moment_polynomial_degree_histogram": {
            str(d): n
            for d, n in sorted(
                Counter(
                    max(sum(power for _, power in unpack(t)) for t in p)
                    for _, _, p in moments
                ).items()
            )
        },
        "moment_monomial_degree_histogram": {
            str(d): n
            for d, n in sorted(
                Counter(
                    sum(power for _, power in unpack(t))
                    for _, _, p in moments
                    for t in p
                ).items()
            )
        },
        "coefficient_histogram": {
            str(c): n
            for c, n in sorted(
                Counter(c for _, _, p in moments for c in p.values()).items()
            )
        },
        "json_file": "exact_f3_math_model.json",
        "json_sha256": hashlib.sha256(encoded.encode()).hexdigest(),
        "input_file": "exact_f3_math_model.ms",
        "input_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "checks": checks,
    }
    return encoded, text, audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    encoded, text, audit = build()
    for name, content in [
        ("exact_f3_math_model.json", encoded),
        ("exact_f3_math_model.ms", text),
        ("exact_f3_math_audit.json", json.dumps(audit, indent=2) + "\n"),
    ]:
        path = HERE / name
        if args.check:
            assert path.read_text() == content
        else:
            path.write_text(content)
    print(
        json.dumps(
            {k: v for k, v in audit.items() if k != "moment_term_count_by_exponents"},
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
