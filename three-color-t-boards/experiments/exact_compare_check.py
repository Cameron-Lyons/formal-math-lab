#!/usr/bin/env python3
"""Check the direct-comparison model against independent exact enumeration."""

import itertools
import json
import sys
import tempfile
from collections import Counter
from pathlib import Path

from exact_compare_cnf import make_compare_cnf
from exact_marginal_check import exact_count
from exact_marginal_cnf import write_cnf
from exact_phase import board_model, normalize_board, rephase

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "sources/anc"))
from count_extensions import count_extensions  # noqa: E402


def main():
    boards, _, _ = count_extensions(2, [])
    assert len(boards) == 168
    reference = Counter("".join(map(str, b[:4])) for b in boards)
    certificate = json.loads((ROOT / "sources/anc/certificates.json").read_text())
    bad = json.loads(
        (ROOT / "experiments/exact_structure_counterexample.json").read_text()
    )["rows"]
    cases = [
        (1, [], False, False, 1, "one color"),
        (2, [], False, False, 168, "binary"),
        (2, [], True, False, 84, "binary palette"),
        (2, [], False, True, 42, "binary orbit"),
    ]
    cases.extend(
        (
            2,
            [prefix[:1], prefix[1:]],
            False,
            False,
            reference[prefix],
            "prefix " + prefix,
        )
        for prefix in map("".join, itertools.product("01", repeat=4))
    )
    cases.extend(
        (3, board, False, False, 1, "ternary witness " + str(i))
        for i, board in enumerate(certificate["ternary_seeds"])
    )
    cases.append((3, bad, False, False, 0, "triple marginal counterexample"))
    with tempfile.TemporaryDirectory(prefix="exact_compare_check_") as directory:
        path = Path(directory) / "case.cnf"
        for colors, prefix, palette, orbit, expected, label in cases:
            cnf, cells, stats = make_compare_cnf(colors, prefix, palette, orbit)
            write_cnf(path, cnf, cells)
            actual = exact_count(path, 60)
            assert actual == expected, (label, actual, expected)
            print(
                json.dumps(
                    {
                        "case": label,
                        "exact_count": actual,
                        "variables": stats["variables"],
                        "clauses": stats["clauses"],
                    }
                ),
                flush=True,
            )
        # Rephasing must preserve the unrestricted count as well.
        cnf, cells, _ = make_compare_cnf(2, orbit_canonical=True)
        rows = ["".join(map(str, boards[0][r * r : (r + 1) ** 2])) for r in range(5)]
        rows = normalize_board(rows, 2, "orbit")
        phased = rephase(cnf, board_model(cnf, cells, rows))
        write_cnf(path, phased, cells)
        assert exact_count(path, 60) == 42
    # Check complete functional assignments for the large, unrestricted model.
    cnf, cells, stats = make_compare_cnf(3, orbit_canonical=True)
    for board in certificate["ternary_seeds"]:
        board_model(cnf, cells, normalize_board(board, 3, "orbit"))
    print(
        json.dumps(
            {
                "exact_count_checks_passed": len(cases) + 1,
                "ternary_models_fully_propagated": len(certificate["ternary_seeds"]),
                "unrestricted_ternary_variables": stats["variables"],
                "unrestricted_ternary_clauses": stats["clauses"],
            }
        ),
        flush=True,
    )


if __name__ == "__main__":
    main()
