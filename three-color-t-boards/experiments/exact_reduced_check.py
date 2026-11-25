#!/usr/bin/env python3
"""Independent finite layout and exact-count checks for the reduced system."""

import itertools
import json
import tempfile
from pathlib import Path

from exact_marginal_check import exact_count
from exact_marginal_cnf import write_cnf
from exact_reduced_cnf import make_reduced_cnf, selected_lines

ROOT = Path(__file__).resolve().parents[1]


def check_layout(colors):
    patterns = set(itertools.product(range(colors), repeat=4))
    pivots = set(itertools.product(range(colors - 1), repeat=4))
    for omit, axes, values in selected_lines(colors):
        pattern: list[int | None] = [None] * 4
        for axis, value in zip(axes, values, strict=False):
            pattern[axis] = value
        pattern[omit] = colors - 1
        assert all(x is not None for x in pattern)
        pivot = tuple(x for x in pattern if x is not None)
        assert pivot not in pivots
        assert next(i for i, x in enumerate(pivot) if x == colors - 1) == omit
        for alternate in range(colors - 1):
            pattern[omit] = alternate
            assert tuple(pattern).count(colors - 1) == pivot.count(colors - 1) - 1
        pivots.add(pivot)
    assert pivots == patterns
    dropped = {((colors - 1,) * 4)}
    remaining = set(itertools.product(range(colors - 1), repeat=4))
    for _omit, axes, values in selected_lines(colors, True):
        entry = [colors - 1] * 4
        for axis, value in zip(axes, values, strict=False):
            entry[axis] = value
        remaining.add(tuple(entry))
    assert remaining == patterns - dropped


def main():
    for colors in (1, 2, 3):
        check_layout(colors)
    certificate = json.loads((ROOT / "sources/anc/certificates.json").read_text())
    counterexample = json.loads(
        (ROOT / "experiments/exact_structure_counterexample.json").read_text()
    )["rows"]
    # Every selected triple constraint really holds on the nonvalid board;
    # the added base-pattern constraints must be what excludes it.
    quads: list[tuple[int, ...]] = [
        (int(counterexample[r - 1][j]), *tuple(map(int, counterexample[r][j : j + 3])))
        for r in range(1, 10)
        for j in range(2 * r - 1)
    ]
    for _, axes, values in selected_lines(3):
        assert sum(tuple(p[a] for a in axes) == values for p in quads) == 3
    assert any(quads.count(p) != 1 for p in itertools.product(range(2), repeat=4))
    checks = 0
    with tempfile.TemporaryDirectory(prefix="exact_reduced_check_") as directory:
        path = Path(directory) / "case.cnf"
        for cardinality, drop in itertools.product(
            ("sequential", "network"), (False, True)
        ):
            for orbit in (False, True):
                cnf, cells, _stats = make_reduced_cnf(
                    2,
                    orbit_canonical=orbit,
                    cardinality=cardinality,
                    drop_one_line=drop,
                )
                write_cnf(path, cnf, cells)
                count = exact_count(path, 60)
                assert count == (42 if orbit else 168), (
                    cardinality,
                    drop,
                    orbit,
                    count,
                )
                checks += 1
                print(
                    json.dumps(
                        {
                            "case": "binary",
                            "orbit": orbit,
                            "drop_one_line": drop,
                            "cardinality": cardinality,
                            "count": count,
                            "variables": cnf.variables,
                            "clauses": len(cnf.clauses),
                        }
                    ),
                    flush=True,
                )
            for rows, expected, label in [
                (certificate["ternary_seeds"][0], 1, "valid ternary board"),
                (counterexample, 0, "uniform-triple counterexample"),
            ]:
                cnf, cells, _ = make_reduced_cnf(
                    3, rows, cardinality=cardinality, drop_one_line=drop
                )
                write_cnf(path, cnf, cells)
                count = exact_count(path, 60)
                assert count == expected, (label, cardinality, drop, count)
                checks += 1
    print(
        json.dumps(
            {
                "exact_count_checks_passed": checks,
                "triangular_layout_palettes": [1, 2, 3],
                "counterexample_satisfies_all_selected_triples": True,
                "counterexample_excluded_by_base_quadruples": True,
            }
        ),
        flush=True,
    )


if __name__ == "__main__":
    main()
