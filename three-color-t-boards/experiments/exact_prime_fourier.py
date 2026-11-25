#!/usr/bin/env python3
"""Geometry-derived Fourier ideals over F_p, p prime and p == 2 (mod 3).

Fixed colors live in F_(p^2)=F_p[a]/(a^2+a+1): 0->1, 1->a,
2->a^2=-1-a. No characteristic-two polynomial lists are imported.
This exports generating ideals and verifies them; it runs no Groebner basis.
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
from collections import Counter, defaultdict
from functools import cache
from math import isqrt
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


@cache
def validate_prime(p):
    if not isinstance(p, int) or isinstance(p, bool) or p < 2 or p % 3 != 2:
        raise ValueError("characteristic must be a prime congruent to 2 modulo 3")
    if p != 2 and p % 2 == 0:
        raise ValueError("characteristic is composite")
    # Exact primality validation, intended for the small experimental primes.
    for divisor in range(3, isqrt(p) + 1, 2):
        if p % divisor == 0:
            raise ValueError("characteristic is composite")
    return p


def placements():
    """Rebuild all centered T placements from row/column coordinates."""
    result = [
        (
            top_row**2 + column,
            (top_row + 1) ** 2 + column,
            (top_row + 1) ** 2 + column + 1,
            (top_row + 1) ** 2 + column + 2,
        )
        for top_row in range(9)
        for column in range(2 * top_row + 1)
    ]
    assert len(result) == 81 and len(set(result)) == 81
    return result


def add(x, y, p):
    return ((x[0] + y[0]) % p, (x[1] + y[1]) % p)


def multiply(x, y, p):
    u, v = x
    s, t = y
    return ((u * s - v * t) % p, (u * t + v * s - v * t) % p)


def power(x, n, p):
    result = (1, 0)
    while n:
        if n & 1:
            result = multiply(result, x, p)
        x = multiply(x, x, p)
        n >>= 1
    return result


def colors(p):
    return ((1, 0), (0, 1), (p - 1, p - 1))


def representatives():
    result = [
        e
        for e in itertools.product(range(3), repeat=4)
        if next((x for x in e if x), 0) == 1
    ]
    assert len(result) == 40
    return result


def validate_prefix(prefix):
    prefix = list(prefix)
    if len(prefix) > 10 or any(
        not isinstance(row, str) or len(row) != 2 * r + 1
        for r, row in enumerate(prefix)
    ):
        raise ValueError("prefix must contain the first rows, with lengths 1,3,...,19")
    if any(c not in "012" for row in prefix for c in row):
        raise ValueError("prefix contains a non-ternary color")
    return prefix


def generate_model(prime, prefix=(), *, all_moments=False):
    """Return an ordinary polynomial generating ideal, never a standard basis.

    Each term has coefficient [u,v] modulo prime and a monomial containing
    [free_variable_index, exponent] pairs. Domains are explicitly included.
    Integer occurrence multiplicities are grouped before reduction modulo p.
    """
    p = validate_prime(prime)
    if not isinstance(all_moments, bool):
        raise TypeError("all_moments must be Boolean")
    prefix = validate_prefix(prefix)
    fixed = [int(c) for row in prefix for c in row]
    free = list(range(len(fixed), 100))
    index = {cell: i for i, cell in enumerate(free)}
    moments: list[dict[str, Any]] = []
    exponents_to_export = (
        [e for e in itertools.product(range(3), repeat=4) if any(e)]
        if all_moments
        else representatives()
    )
    for exponents in exponents_to_export:
        groups = defaultdict(lambda: [0, 0, 0])
        for window in placements():
            monomial = []
            character = 0
            for cell, exponent in zip(window, exponents, strict=False):
                if cell < len(fixed):
                    character += fixed[cell] * exponent
                elif exponent:
                    monomial.append((index[cell], exponent))
            groups[tuple(sorted(monomial))][character % 3] += 1
        terms: list[dict[str, Any]] = []
        integer_groups: list[dict[str, Any]] = []
        for monomial, multiplicities in sorted(groups.items()):
            n0, n1, n2 = multiplicities
            coefficient = [(n0 - n2) % p, (n1 - n2) % p]
            pairs = [list(pair) for pair in monomial]
            integer_groups.append(
                {"monomial": pairs, "root_multiplicities": multiplicities}
            )
            if coefficient != [0, 0]:
                terms.append({"coefficient": coefficient, "monomial": pairs})
        assert sum(sum(g["root_multiplicities"]) for g in integer_groups) == 81
        moments.append(
            {
                "role_exponents": list(exponents),
                "rhs": [0, 0],
                "terms": terms,
                "integer_occurrence_groups": integer_groups,
            }
        )
    domains = [
        {
            "variable": i,
            "terms": [
                {"coefficient": [1, 0], "monomial": [[i, 3]]},
                {"coefficient": [p - 1, 0], "monomial": []},
            ],
        }
        for i in range(len(free))
    ]
    return {
        "format": "t-board-prime-fourier-v1",
        "coefficient_characteristic": p,
        "coefficient_field": f"F_{p}[a]/(a^2+a+1)",
        "extension_polynomial": "a^2+a+1",
        "height": 10,
        "variables": len(free),
        "color_values": [list(value) for value in colors(p)],
        "prefix": prefix,
        "free_original_cells": free,
        "placements": [list(w) for w in placements()],
        "domain_equations": domains,
        "moment_equations": moments,
        "all_nonconstant_moments": all_moments,
        "moment_equation_count": len(moments),
        "frobenius_redundant_equations": 40 if all_moments else 0,
        "frobenius_pair_rule": "first nonzero exponent equals 1",
        "requires_quadratic_coefficients": any(
            term["coefficient"][1] for equation in moments for term in equation["terms"]
        ),
        "zeroth_moment": [81 % p, 0],
        "count_scope": "full labeled boards"
        if not prefix
        else "extensions of fixed prefix",
        "standard_basis_complete": False,
        "status": "UNEVALUATED_GENERATING_IDEAL",
    }


def evaluate_equation(equation, values, prime):
    value = (0, 0)
    for term in equation["terms"]:
        product = tuple(term["coefficient"])
        for variable, exponent in term["monomial"]:
            product = multiply(product, power(values[variable], exponent, prime), prime)
        value = add(value, product, prime)
    rhs = equation.get("rhs", [0, 0])
    return ((value[0] - rhs[0]) % prime, (value[1] - rhs[1]) % prime)


def direct_transform(pattern_counts, exponents, prime):
    """Independent character transform of the integer pattern-count table."""
    roots = colors(prime)
    result = (0, 0)
    for pattern, multiplicity in pattern_counts.items():
        value = (multiplicity % prime, 0)
        for color, exponent in zip(pattern, exponents, strict=False):
            # Use field powers rather than the generator's exponent grouping.
            value = multiply(value, power(roots[color], exponent, prime), prime)
        result = add(result, value, prime)
    return result


def check_models(primes=(5, 29, 83), random_boards=12):
    rng = random.Random(0x5052494D45)
    certificate = json.loads((ROOT / "sources/anc/certificates.json").read_text())
    known = list(certificate["ternary_seeds"])
    extended_path = ROOT / "extended_seeds.json"
    if extended_path.exists():
        known.extend(entry["rows"] for entry in json.loads(extended_path.read_text()))
    gauge_path = ROOT / "experiments/exact_structure_gauge_certificate.json"
    if gauge_path.exists():
        for entry in json.loads(gauge_path.read_text())["boards"]:
            flat = entry["flat"]
            known.append([flat[r * r : (r + 1) ** 2] for r in range(10)])
    known = sorted({tuple(rows) for rows in known})
    invalid = json.loads(
        (ROOT / "experiments/exact_structure_counterexample.json").read_text()
    )["rows"]
    reports = []
    for p in primes:
        model = generate_model(p)
        full_model = generate_model(p, all_moments=True)
        all_equations = {
            tuple(eq["role_exponents"]): eq for eq in full_model["moment_equations"]
        }
        representative_keys = {
            tuple(eq["role_exponents"]) for eq in model["moment_equations"]
        }
        assert len(all_equations) == 80
        assert all(
            eq == all_equations[tuple(eq["role_exponents"])]
            for eq in model["moment_equations"]
        )
        roots = colors(p)
        assert len(set(roots)) == 3 and all(power(z, 3, p) == (1, 0) for z in roots)
        assert all(power(z, p, p) == power(z, 2, p) for z in roots)
        assert all((x * x + x + 1) % p for x in range(p))
        # Tiny domain and root-sum fixtures, checked by exhaustive color choices.
        root_sum_count = sum(
            add(add(x, y, p), z, p) == (0, 0)
            for x, y, z in itertools.product(roots, repeat=3)
        )
        assert root_sum_count == 6
        assert len(list(itertools.product(roots, repeat=2))) == 9
        random_equations = 0
        for _ in range(random_boards):
            rows = [
                "".join(str(rng.randrange(3)) for _ in range(2 * r + 1))
                for r in range(10)
            ]
            flat = [int(c) for row in rows for c in row]
            counts = Counter(
                tuple(flat[cell] for cell in window) for window in placements()
            )
            values = [roots[color] for color in flat]
            for prefix_rows in (0, 1, 6, 9, 10):
                partial_model = (
                    model if prefix_rows == 0 else generate_model(p, rows[:prefix_rows])
                )
                complete_moments = (
                    full_model
                    if prefix_rows == 0
                    else generate_model(p, rows[:prefix_rows], all_moments=True)
                )
                partners = {
                    tuple(eq["role_exponents"]): eq
                    for eq in complete_moments["moment_equations"]
                }
                assert all(
                    eq == partners[tuple(eq["role_exponents"])]
                    for eq in partial_model["moment_equations"]
                )
                partial = [
                    values[cell] for cell in partial_model["free_original_cells"]
                ]
                for equation in partial_model["moment_equations"]:
                    e = tuple(equation["role_exponents"])
                    value = evaluate_equation(equation, partial, p)
                    assert value == direct_transform(counts, e, p)
                    conjugate = direct_transform(counts, tuple(2 * x % 3 for x in e), p)
                    assert power(value, p, p) == conjugate
                    partner = partners[tuple(2 * x % 3 for x in e)]
                    assert evaluate_equation(partner, partial, p) == conjugate
                    random_equations += 1
                assert all(
                    evaluate_equation(eq, partial, p) == (0, 0)
                    for eq in partial_model["domain_equations"]
                )
        valid_count = 0
        for rows in known:
            flat = [int(c) for row in rows for c in row]
            assert (
                len({tuple(flat[c] for c in window) for window in placements()}) == 81
            )
            values = [roots[color] for color in flat]
            assert all(
                evaluate_equation(eq, values, p) == (0, 0)
                for eq in model["moment_equations"]
            )
            assert all(
                evaluate_equation(eq, values, p) == (0, 0)
                for eq in full_model["moment_equations"]
                if tuple(eq["role_exponents"]) not in representative_keys
            )
            valid_count += 1
        # Full fixed valid boards give the zero ideal in zero variables.
        for rows in certificate["ternary_seeds"]:
            fixed_model = generate_model(p, rows)
            assert fixed_model["variables"] == 0 and not fixed_model["domain_equations"]
            assert all(not eq["terms"] for eq in fixed_model["moment_equations"])
            assert all(
                not eq["terms"]
                for eq in generate_model(p, rows, all_moments=True)["moment_equations"]
            )
        fixed_bad = generate_model(p, invalid)
        bad_equations = sum(bool(eq["terms"]) for eq in fixed_bad["moment_equations"])
        assert bad_equations > 0
        bad_all = sum(
            bool(eq["terms"])
            for eq in generate_model(p, invalid, all_moments=True)["moment_equations"]
        )
        assert bad_all == 2 * bad_equations
        # Four coordinates form an invertible character basis: its 3x3
        # Vandermonde determinant is a product of distinct-root differences.
        determinant = (1, 0)
        for i, j in itertools.combinations(range(3), 2):
            determinant = multiply(
                determinant,
                ((roots[j][0] - roots[i][0]) % p, (roots[j][1] - roots[i][1]) % p),
                p,
            )
        assert determinant != (0, 0)
        reports.append(
            {
                "prime": p,
                "status": "PASS",
                "full_variables": model["variables"],
                "domain_equations": len(model["domain_equations"]),
                "moments": len(model["moment_equations"]),
                "full_moment_terms": sum(
                    len(eq["terms"]) for eq in model["moment_equations"]
                ),
                "random_board_equation_comparisons": random_equations,
                "known_valid_boards_checked": valid_count,
                "full_fixed_valid_boards_checked": len(certificate["ternary_seeds"]),
                "invalid_full_fixed_nonzero_equations": bad_equations,
                "all80_export_checked": True,
                "all80_frobenius_partner_value_checks": random_equations,
                "all80_invalid_full_fixed_nonzero_equations": bad_all,
                "tiny_domain_pair_count": 9,
                "tiny_root_sum_count": root_sum_count,
                "no_standard_basis_or_counting_trial": True,
            }
        )
    result = {"status": "PASS", "primes": list(primes), "checks": reports}
    (ROOT / "experiments/exact_prime_fourier_checks.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, default=29)
    parser.add_argument("--prefix-json", type=Path)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--prefix-rows", type=int, default=0)
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--all-moments", action="store_true", help="Export all 80 nonconstant moments."
    )
    parser.add_argument("output", type=Path, nargs="?")
    args = parser.parse_args()
    if args.check:
        print(json.dumps(check_models(), indent=2))
        return
    if args.output is None:
        parser.error("an output path or --check is required")
    if not 0 <= args.prefix_rows <= 10:
        parser.error("prefix rows must lie between 0 and 10")
    prefix = []
    if args.prefix_json:
        data = json.loads(args.prefix_json.read_text())
        if isinstance(data, dict):
            data = data["ternary_seeds"][args.seed]
        prefix = data[: args.prefix_rows]
    elif args.prefix_rows:
        parser.error("a nonempty prefix requires --prefix-json")
    model = generate_model(args.prime, prefix, all_moments=args.all_moments)
    args.output.write_text(json.dumps(model, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: model[k]
                for k in (
                    "format",
                    "coefficient_characteristic",
                    "variables",
                    "requires_quadratic_coefficients",
                    "status",
                )
            }
        )
    )


if __name__ == "__main__":
    main()
