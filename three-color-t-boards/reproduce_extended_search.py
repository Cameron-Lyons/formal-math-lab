#!/usr/bin/env python3
"""Rediscover the larger recorded family without overwriting certificates.

Requires a C++17 compiler (g++ by default). The seed1 search stops after the
recorded number of new orbits, so its output does not depend on reproducing
a 180-second timing cutoff. A separate safety timeout can still stop slow runs.
This optional discovery replay is not required to check the Lean certificates.
"""
import argparse
from collections import Counter
from itertools import permutations, product
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent


def jsonl_rows(path):
    if not path.exists():
        return []
    return [json.loads(line)["rows"] for line in path.read_text().splitlines()]


def orbit_flat(rows):
    return {
        "".join(str(p[int(c)]) for row in rows
                for c in (row[::-1] if reflected else row))
        for p in permutations(range(3)) for reflected in (False, True)
    }


def verify_board(rows):
    if len(rows) != 10 or any(len(row) != 2 * r + 1 for r, row in enumerate(rows)):
        raise ValueError("rediscovered board has incorrect row lengths")
    if any(c not in "012" for row in rows for c in row):
        raise ValueError("rediscovered board has invalid colors")
    grid = {(j - r, -r): int(c) for r, row in enumerate(rows) for j, c in enumerate(row)}
    actual = Counter()
    for x, y in grid:
        cells = [(x, y + 1), (x - 1, y), (x, y), (x + 1, y)]
        if all(cell in grid for cell in cells):
            actual[tuple(grid[cell] for cell in cells)] += 1
    if actual != Counter({pattern: 1 for pattern in product(range(3), repeat=4)}):
        raise ValueError("rediscovered board fails geometric pattern verification")


def run_search(command, directory, output, expected, label):
    result = subprocess.run(command, cwd=directory, text=True, capture_output=True)
    lines = result.stderr.splitlines()
    status_line = lines[-1] if lines else "no final search status"
    actual = jsonl_rows(output)
    if result.returncode:
        raise RuntimeError(
            f"{label} stopped before successful completion: {status_line}. "
            f"Recovered {len(actual)} records. Increase --seconds to allow more time; "
            "a timeout does not imply nonexistence or an exact count."
        )
    if actual != expected:
        first = next((i for i, pair in enumerate(zip(actual, expected))
                      if pair[0] != pair[1]), min(len(actual), len(expected)))
        raise ValueError(f"{label}: ordered row-list mismatch at record {first}; "
                         f"got {len(actual)}, expected {len(expected)}")
    for rows in actual:
        verify_board(rows)
    print(f"{label}: matched and geometrically verified all {len(actual)} recorded new orbits.")
    print(status_line)
    return status_line


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds", type=int, default=300,
                        help="safety time limit for each search (default: 300)")
    parser.add_argument("--smoke", action="store_true",
                        help="only rediscover and verify the first seed1 record")
    parser.add_argument("--compiler", default="g++", help="C++17 compiler (default: g++)")
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error("--seconds must be positive")
    seeds = json.loads((ROOT / "sources/anc/certificates.json").read_text())["ternary_seeds"]
    original = json.loads((ROOT / "prefix_result.json").read_text())["rows"]
    known = set().union(*(orbit_flat(rows) for rows in seeds + [original]))
    if len(known) != 72:
        raise ValueError("expected 72 known labeled boards from the six original orbits")
    expected1 = jsonl_rows(ROOT / "more_results.jsonl")
    if args.smoke:
        expected1 = expected1[:1]
    if not expected1:
        raise ValueError("recorded seed1 certificates are empty")

    with tempfile.TemporaryDirectory(prefix="tboard-extended-replay-") as tmp:
        directory = Path(tmp)
        (directory / "prefix_known.txt").write_text("\n".join(sorted(known)) + "\n")
        # extended_search.cpp also looks for this original certificate; keeping
        # it in the working directory preserves the original search environment.
        (directory / "prefix_result.json").write_bytes((ROOT / "prefix_result.json").read_bytes())
        names = ["more_search"] if args.smoke else ["extended_search", "more_search"]
        for name in names:
            subprocess.run([args.compiler, "-O3", "-std=c++17", str(ROOT / f"{name}.cpp"),
                            "-o", str(directory / name)], check=True)

        if not args.smoke:
            output0 = directory / "prefix0.jsonl"
            status0 = run_search(
                [str(directory / "extended_search"), "".join(seeds[0][:6]), "6",
                 str(args.seconds), str(output0)],
                directory, output0, jsonl_rows(ROOT / "extended_prefix0.jsonl"), "prefix0",
            )
            if "exhaustive=1" not in status0:
                raise RuntimeError("prefix0 did not report exhaustive completion")
            print("prefix0: complete enumeration of this fixed prefix only; "
                  "enumeration completeness is not a Lean theorem.")

        output1 = directory / "seed1.jsonl"
        status1 = run_search(
            [str(directory / "more_search"), "".join(seeds[1][:6]), "6",
             str(args.seconds), str(directory / "prefix_known.txt"), str(output1),
             str(len(expected1))],
            directory, output1, expected1, "seed1",
        )
        if "termination=count_limit" not in status1 or "exhaustive=0" not in status1:
            raise RuntimeError("seed1 did not report the intended count-limit stop")
        print("seed1: stopped at the requested new-orbit count; search is not exhaustive.")
        print("Smoke replay passed." if args.smoke else "Full recorded discovery replay passed.")
        print("Existing certificates were not modified. No unrestricted exact count is claimed.")


if __name__ == "__main__":
    main()
