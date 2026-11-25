#!/usr/bin/env python3
"""Independent finite-box checks for the standard-monomial counter."""

import itertools
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

from exact_standard_monomials import (
    CountLimitExceeded,
    MissingPurePowerBounds,
    count_standard_monomials,
)

HERE = Path(__file__).resolve().parent


def powers(bounds):
    return [
        tuple(bound if j == i else 0 for j in range(len(bounds)))
        for i, bound in enumerate(bounds)
    ]


def direct(bounds, generators):
    return sum(
        not any(
            all(g <= e for g, e in zip(generator, exponents, strict=False))
            for generator in generators
        )
        for exponents in itertools.product(*(range(b) for b in bounds))
    )


def fibonacci(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def check(generators, variables, expected):
    stats = {}
    actual = count_standard_monomials(
        generators, variables, standard_basis_complete=True, stats=stats
    )
    assert isinstance(actual, int) and actual == expected, (
        generators,
        actual,
        expected,
    )
    return stats


def rejects(call, kind):
    try:
        call()
    except kind:
        return
    raise AssertionError(f"expected {kind.__name__}")


def main():
    fixed = [
        ([], 0, 1),
        ([()], 0, 0),
        ([[0, 0, 0, 0]], 4, 0),
        (powers([3, 4]), 2, 12),
        ([*powers([3, 4]), (1, 2)], 2, 8),
        ([*powers([3, 3]), (2, 1), (1, 2)], 2, 6),
        ([*powers([2, 2, 2]), (1, 1, 0), (1, 0, 1), (0, 1, 1)], 3, 4),
        ([*powers([2, 2, 5, 4, 7]), (1, 1, 0, 0, 0), (0, 0, 2, 1, 0)], 5, 231),
    ]
    for generators, n, expected in fixed:
        check(generators, n, expected)
    redundant_stats = check(
        [*powers([4, 4]), (1, 1), (2, 1), (2, 2), (3, 3), (1, 1)], 2, 7
    )
    assert redundant_stats["antichain_removed"] > 0
    # Splitting must use intervals, not iterate over these huge pure bounds.
    huge_bound = 10**80
    huge_stats = check(
        [*powers([huge_bound, huge_bound]), (1, 1)], 2, 2 * huge_bound - 1
    )
    assert huge_stats["states"] < 10

    rng = random.Random(0x5354414952)
    random_checks = 0
    for special in (False, True):
        for _ in range(375):
            n = rng.randint(2, 6) if special else rng.randint(0, 6)
            bounds = [
                rng.randint(2, 4) if special else rng.randint(1, 4) for _ in range(n)
            ]
            generators = powers(bounds)
            for _ in range(rng.randrange(10)):
                support = rng.sample(
                    range(n), rng.randint(2, n) if special else rng.randint(0, n)
                )
                row = [0] * n
                for i in support:
                    row[i] = (
                        rng.randint(1, bounds[i] - 1)
                        if special
                        else rng.randint(1, bounds[i] + 1)
                    )
                generators.append(tuple(row))
            rng.shuffle(generators)
            check(generators, n, direct(bounds, generators))
            random_checks += 1

    cubes = powers([3] * 100)
    cube_count = 3**100
    cube_stats = check(cubes, 100, cube_count)
    assert cube_stats["states"] == 1 and cube_stats["box_leaves"] == 1
    decimal_count = 10**20
    decimal_stats = check(powers([10] * 20), 20, decimal_count)
    mixed_stats = check([*cubes, (1,) * 100], 100, 3**100 - 2**100)
    path = powers([2] * 100)
    for i in range(99):
        path.append(tuple(int(j in (i, i + 1)) for j in range(100)))
    path_count = fibonacci(102)
    path_stats = check(path, 100, path_count)
    assert path_stats["cache_hits"] > 0
    assert path_stats["component_factorizations"] > 0

    failure_tests = [
        (lambda: count_standard_monomials([[2]], 1), ValueError),
        (
            lambda: count_standard_monomials([[2]], 1, standard_basis_complete="true"),
            ValueError,
        ),
        (
            lambda: count_standard_monomials([], 2, standard_basis_complete=True),
            MissingPurePowerBounds,
        ),
        (
            lambda: count_standard_monomials(
                [[2, 0], [1, 1]], 2, standard_basis_complete=True
            ),
            MissingPurePowerBounds,
        ),
        (
            lambda: count_standard_monomials(
                [[2, -1]], 2, standard_basis_complete=True
            ),
            ValueError,
        ),
        (
            lambda: count_standard_monomials([[2.0]], 1, standard_basis_complete=True),
            ValueError,
        ),
        (
            lambda: count_standard_monomials([[True]], 1, standard_basis_complete=True),
            ValueError,
        ),
        (
            lambda: count_standard_monomials([[2]], 2, standard_basis_complete=True),
            ValueError,
        ),
        (
            lambda: count_standard_monomials(
                [[2]], 1, standard_basis_complete=True, max_states=0
            ),
            ValueError,
        ),
        (
            lambda: count_standard_monomials(
                [*powers([2, 2]), (1, 1)], 2, standard_basis_complete=True, max_states=1
            ),
            CountLimitExceeded,
        ),
    ]
    for call, kind in failure_tests:
        rejects(call, kind)

    with tempfile.TemporaryDirectory(prefix="exact_standard_monomials_") as directory:
        source = Path(directory) / "leading.json"
        source.write_text(
            json.dumps(
                {
                    "format": "leading-monomial-ideal-v1",
                    "variables": 100,
                    "standard_basis_complete": True,
                    "leading_monomials": cubes,
                    "provenance": {
                        "kind": "pure monomial ideal; its generators are a standard basis"
                    },
                }
            )
        )
        completed = subprocess.run(
            [sys.executable, str(HERE / "exact_standard_monomials.py"), str(source)],
            check=True,
            capture_output=True,
            text=True,
        )
        assert json.loads(completed.stdout)["dimension_decimal"] == str(cube_count)
        document = json.loads(source.read_text())
        document["standard_basis_complete"] = False
        source.write_text(json.dumps(document))
        rejected = subprocess.run(
            [sys.executable, str(HERE / "exact_standard_monomials.py"), str(source)],
            capture_output=True,
            text=True,
            check=False,
        )
        assert rejected.returncode != 0 and not rejected.stdout

    report = {
        "status": "PASS",
        "fixed_fixtures": len(fixed) + 2,
        "randomized_direct_enumeration_checks": random_checks,
        "explicit_rejection_checks": len(failure_tests),
        "cli_checks": 2,
        "pure_cubic_100_dimension_decimal": str(cube_count),
        "pure_cubic_stats": cube_stats,
        "pure_decimal_20_dimension_decimal": str(decimal_count),
        "pure_decimal_stats": decimal_stats,
        "mixed_cubic_100_dimension_decimal": str(3**100 - 2**100),
        "mixed_cubic_stats": mixed_stats,
        "binary_path_100_dimension_decimal": str(path_count),
        "binary_path_stats": path_stats,
        "no_polynomial_generating_set_counted_without_standard_basis_attestation": True,
    }
    (HERE / "exact_standard_monomials_check_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
