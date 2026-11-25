#!/usr/bin/env python3
"""Finite arithmetic checks for a hypothetical field-priority F4 invariant.
No native solver, implementation patch, or current-build bound is asserted.
"""

import argparse
import hashlib
import json
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent


def lead(poly):
    return max(poly, key=lambda t: (sum(t), tuple(-v for v in reversed(t))))


def add(a, b, scale=1):
    out = a.copy()
    for t, c in b.items():
        v = (out.get(t, 0) + scale * c) % 3
        if v:
            out[t] = v
        elif t in out:
            del out[t]
    return out


def multiply(poly, monomial):
    return {
        tuple(a + b for a, b in zip(t, monomial, strict=False)): c
        for t, c in poly.items()
    }


def lcm(a, b):
    return tuple(max(x, y) for x, y in zip(a, b, strict=False))


def quotient(a, b):
    assert all(x >= y for x, y in zip(a, b, strict=False))
    return tuple(x - y for x, y in zip(a, b, strict=False))


def spoly(a, b):
    la, lb = lead(a), lead(b)
    L = lcm(la, lb)
    return add(multiply(a, quotient(L, la)), multiply(b, quotient(L, lb)), -1)


def record(poly):
    return [[c, list(t)] for t, c in sorted(poly.items())]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def build():
    # Per-coordinate inequalities imply the bounds in every dimension.
    nn = []
    cn = []
    normal = []
    for a, b, t in product(range(3), repeat=3):
        exponent = max(a, b) - a + t
        assert exponent <= 4
        nn.append(exponent)
    for a, t in product(range(3), repeat=2):
        exponent = 3 - a + t
        assert exponent <= 5
        cn.append(exponent)
    for m in range(3):
        for a in range(m + 1):
            for t in range(3):
                exponent = m - a + t
                assert exponent <= 4
                normal.append(exponent)
    high_steps = 0
    for m in product(range(6), repeat=4):
        for i, e in enumerate(m):
            if e < 3:
                continue
            tail = list(m)
            tail[i] -= 2
            assert max(tail) <= 5 and sum(tail) == sum(m) - 2
            assert all(tail[j] <= m[j] for j in range(4))
            high_steps += 1
    # Cube/cube row construction: total degree6 is not coordinate6.
    cube_pair_checks = 0
    for n in range(1, 5):
        for i in range(n):
            for j in range(n):
                a = tuple(3 * int(v == i) for v in range(n))
                b = tuple(3 * int(v == j) for v in range(n))
                L = lcm(a, b)
                for original, which in ((a, i), (b, j)):
                    tail = tuple(int(v == which) for v in range(n))
                    result = tuple(
                        x + y for x, y in zip(quotient(L, original), tail, strict=False)
                    )
                    assert max(result) <= 3 and max(L) <= 3
                    cube_pair_checks += 1
    # Degree-five coordinate can occur in an ordinary initial pair multiple.
    # The product criterion would normally discard this coprime pair.
    fy = {(0, 3): 1, (0, 1): 2}
    g = {(2, 0): 1, (0, 2): 1}
    L = lcm(lead(fy), lead(g))
    row = multiply(g, quotient(L, lead(g)))
    assert max(max(t) for t in row) == 5
    # Without field priority, a legitimate normal reducer at an initially
    # introduced high monomial can create exponent6. This is a local symbolic
    # construction, not a claimed trace of the current degree scheduler.
    A = {(2, 2, 0, 0): 1, (2, 0, 0, 2): 1}
    B = {(0, 2, 2, 2): 1, (0, 0, 0, 0): 1}
    C = {(2, 0, 1, 0): 1, (0, 0, 1, 2): 1}
    la, lb, lc = lead(A), lead(B), lead(C)
    assert (la, lb, lc) == ((2, 2, 0, 0), (0, 2, 2, 2), (2, 0, 1, 0))
    assert any(
        min(x, y) > 0 for x, y in zip(la, lb, strict=False)
    )  # product criterion not automatic
    assert not all(x <= y for x, y in zip(lc, la, strict=False))
    assert not all(x <= y for x, y in zip(lc, lb, strict=False))
    seed = multiply(A, quotient(lcm(la, lb), la))
    m = (2, 0, 2, 4)
    assert m in seed
    arbitrary = multiply(C, quotient(m, lc))
    assert (0, 0, 2, 6) in arbitrary
    priority_tail = tuple(x - 2 * int(i == 3) for i, x in enumerate(m))
    assert priority_tail == (2, 0, 2, 2)
    # Omitting field-vs-normal pairs is unsound, even when a normal leading
    # monomial already divides the field cube's leading monomial.
    F = {(3,): 1, (1,): 2}
    G = {(2,): 1, (0,): 1}
    first = spoly(F, G)
    assert first == {(1,): 1}
    second = spoly(G, first)
    assert second == {(0,): 1}
    assert all(not ((x**3 - x) % 3 == 0 and (x * x + 1) % 3 == 0) for x in range(3))
    # Blindly reducing a retained domain against the same cached domain gives
    # zero; dropping both from the logical output would lose the ideal.
    assert add(F, F, -1) == {}
    sources = {}
    source_root = (
        HERE
        / "exact_msolve_byte_exponent_tools/msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb"
    )
    for name in ("symbol.c", "hash.c", "f4.c", "la_ff_8.c"):
        path = source_root / name
        sources[str(path.relative_to(HERE))] = sha(path.read_bytes())
    return {
        "status": "PASS",
        "scope": "conditional mathematical bound for a proposed field-priority ordinary F4 algorithm; no current-build bound or implementation",
        "ordinary_ring": "F3[x1,...,xn], with retained original xi^3-xi equations",
        "per_coordinate_finite_checks": {
            "normal_normal_seed_cases": len(nn),
            "normal_normal_max": max(nn),
            "cube_normal_distinguished_coordinate_cases": len(cn),
            "cube_normal_max": max(cn),
            "normal_column_reduction_cases": len(normal),
            "normal_column_reduction_max": max(normal),
            "four_variable_priority_field_steps": high_steps,
            "cube_cube_row_checks": cube_pair_checks,
        },
        "conditional_coordinate_bound": 5,
        "conditional_final_interreduction_bound": 4,
        "bound_requires_all_nondomain_basis_terms_field_normal": True,
        "bound_requires_high_coordinate_field_priority": True,
        "bound_requires_only_standard_pair_seeds_or_unmultiplied_basis_seeds": True,
        "bound_requires_symbolic_closure_and_normal_new_rows": True,
        "matrix_coefficient_operations_create_no_new_monomials": True,
        "sharp_seed_example": {
            "variables": ["x", "y"],
            "field": record(fy),
            "normal": record(g),
            "normal_pair_multiple": record(row),
            "max_coordinate": 5,
            "product_criterion_can_discard_this_example": True,
        },
        "no_priority_local_counterexample": {
            "variables": ["x", "z", "w", "y"],
            "A": record(A),
            "B": record(B),
            "C": record(C),
            "initial_A_multiple": record(seed),
            "processed_monomial": list(m),
            "ordinary_C_multiple": record(arbitrary),
            "generated_coordinate": 6,
            "priority_field_tail": list(priority_tail),
            "scope": "admissible local construction under ordinary arbitrary reducer selection; not a claimed current-solver execution trace",
        },
        "missing_field_pair_counterexample": {
            "variables": ["x"],
            "F": record(F),
            "G": record(G),
            "S_F_G": record(first),
            "S_G_x": record(second),
            "actual_solution_count": 0,
            "incorrect_standard_monomial_count_if_F_G_are_mistaken_for_a_completed_basis": 2,
        },
        "self_reduction_warning": {
            "input_field": record(F),
            "naive_self_remainder": [],
            "rule": "Do not remove the original field ideal by reducing a retained field generator against its own cached copy and discarding both.",
        },
        "source_snapshot_sha256": sources,
        "source_snapshot_purpose": "ownership/call-path references only; these files do not implement the proposed priority policy",
        "generator_sha256": sha(Path(__file__).read_bytes()),
        "native_solver_invocations": 0,
        "source_files_modified": [],
        "current_nibble_bound_policy": "unchanged: future/current nibble arithmetic must fail closed above15; this conditional proof does not justify dropping checks or claiming bound5 for it",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = build()
    text = json.dumps(result, indent=2) + "\n"
    path = HERE / "exact_f3_priority_bounds.json"
    if args.check:
        assert path.read_text() == text
    else:
        path.write_text(text)
    print(
        json.dumps(
            {
                k: result[k]
                for k in (
                    "status",
                    "scope",
                    "per_coordinate_finite_checks",
                    "native_solver_invocations",
                )
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
