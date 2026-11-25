#!/usr/bin/env python3
"""Compare every CNF encoding against independently known exact counts."""

from __future__ import annotations

import argparse
import itertools
import json
import re
import subprocess
import tempfile
import time
from pathlib import Path

from exact_count_cnf import (
    CNF,
    add_palette_normalization,
    add_reflection_normalization,
    make_cnf,
    mirror_indices,
)

ROOT = Path(__file__).resolve().parents[1]


def check_known_orbits():
    """Check actual symmetry CNF against the explicit lexicographic orbit minimum."""
    cnf = CNF()
    cells = {pos: [cnf.variable() for _ in range(3)] for pos in range(100)}
    add_palette_normalization(cnf, cells, 3)
    comparisons = add_reflection_normalization(cnf, cells, 3)
    # A board supplies one-hot cell values directly; all prefix auxiliaries
    # have their unique values, fixed by the equivalences in the generator.
    masks = [
        (
            sum(1 << (v - 1) for v in set(clause) if v > 0),
            sum(1 << (-v - 1) for v in set(clause) if v < 0),
        )
        for clause in cnf.clauses
    ]
    mirrors = mirror_indices(3)
    seeds = json.loads((ROOT / "extended_seeds.json").read_text())
    images_checked = 0
    for entry in seeds:
        rows = entry["rows"]
        patterns = {
            tuple(map(int, (rows[r - 1][j], *rows[r][j : j + 3])))
            for r in range(1, 10)
            for j in range(2 * r - 1)
        }
        if len(patterns) != 81:
            raise AssertionError("invalid known board")
        orbit = {
            tuple(p[int(c)] for row in rows for c in (row[::-1] if rev else row))
            for p in itertools.permutations(range(3))
            for rev in (False, True)
        }
        if len(orbit) != 12:
            raise AssertionError("expected 12 symmetry images")
        minimum = min(orbit)
        accepted = 0
        for flat in orbit:
            assignment = sum(
                1 << (cells[pos][color] - 1) for pos, color in enumerate(flat)
            )
            for permutation, prefixes in comparisons:
                assignment |= 1 << (prefixes[0] - 1)
                equal = True
                for pos, mirror in enumerate(mirrors):
                    equal = equal and flat[pos] == permutation[flat[mirror]]
                    if equal:
                        assignment |= 1 << (prefixes[pos + 1] - 1)
            satisfies = all(
                (positive & assignment) or (negative & ~assignment)
                for positive, negative in masks
            )
            if bool(satisfies) != (flat == minimum):
                raise AssertionError(
                    ("symmetry CNF disagrees with orbit minimum", entry["index"])
                )
            accepted += bool(satisfies)
            images_checked += 1
        if accepted != 1:
            raise AssertionError("symmetry encoding did not select exactly one image")
    print(
        json.dumps(
            {
                "case": "known ternary orbits",
                "orbits": len(seeds),
                "images": images_checked,
                "canonical_images": len(seeds),
            }
        ),
        flush=True,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--solver", type=Path, default=ROOT / "experiments/exact_count_tools/ganak"
    )
    parser.add_argument("--ternary-prefixes", action="store_true")
    parser.add_argument("--known-orbits", action="store_true")
    parser.add_argument("--seconds", type=float, default=60)
    args = parser.parse_args()
    data = json.loads((ROOT / "sources/anc/certificates.json").read_text())
    cases = [
        (1, [], False, False, 1, "one color"),
        (2, [], False, False, 168, "binary unrestricted"),
        (2, [], True, False, 84, "binary palette normalized"),
        (2, [], True, True, 42, "binary full-orbit normalized"),
        (3, data["ternary_seeds"][0], False, False, 1, "complete ternary witness"),
        (3, ["0", "000", "00000"], False, False, 0, "repeated prefix pattern"),
    ]
    if args.ternary_prefixes:
        cases += [
            (3, rows, False, False, 2, f"published prefix {name}")
            for name, rows in data["ternary_prefixes"].items()
        ]
    with tempfile.TemporaryDirectory(prefix="exact_count_check_") as directory:
        path = Path(directory) / "case.cnf"
        for amo in ["none", "pairwise", "binary", "tree"]:
            for colors, prefix, canonical, orbit, expected, label in cases:
                cnf, _cells = make_cnf(colors, prefix, canonical, amo, orbit)
                with path.open("w") as file:
                    # All variables are counted: no projected-count assumptions.
                    file.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
                    for clause in cnf.clauses:
                        file.write(" ".join(map(str, clause)) + " 0\n")
                started = time.monotonic()
                result = subprocess.run(
                    [
                        str(args.solver),
                        "--prob",
                        "0",
                        "--arjun",
                        "0",
                        "--puura",
                        "0",
                        "--td",
                        "0",
                        "--maxcache",
                        "256",
                        str(path),
                    ],
                    text=True,
                    capture_output=True,
                    timeout=args.seconds,
                    check=False,
                )
                match = re.search(
                    r"^c s exact arb int (\d+)$", result.stdout, re.MULTILINE
                )
                if result.returncode or not match:
                    raise RuntimeError(
                        f"{label}, {amo}: counter failure\n{result.stdout}\n{result.stderr}"
                    )
                actual = int(match[1])
                if actual != expected:
                    raise AssertionError((label, amo, expected, actual))
                print(
                    json.dumps(
                        {
                            "case": label,
                            "amo": amo,
                            "count": actual,
                            "seconds": round(time.monotonic() - started, 3),
                        }
                    ),
                    flush=True,
                )
    if args.known_orbits:
        check_known_orbits()
    print("All exact-count cross-checks passed.")


if __name__ == "__main__":
    main()
