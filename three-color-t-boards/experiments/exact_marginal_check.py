#!/usr/bin/env python3
"""Check marginal encodings by ordinary, unprojected exact model counts."""

from __future__ import annotations

import argparse
import itertools
import json
import math
import re
import subprocess
import tempfile
import time
from pathlib import Path

from exact_count_cnf import CNF
from exact_marginal_cnf import FunctionalGates, make_marginal_cnf, write_cnf

ROOT = Path(__file__).resolve().parents[1]
SOLVER = ROOT / "experiments/exact_count_tools/ganak"


def exact_count(path, seconds):
    result = subprocess.run(
        [
            str(SOLVER),
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
        capture_output=True,
        text=True,
        timeout=seconds,
        check=False,
    )
    match = re.search(r"^c s exact arb int (\d+)$", result.stdout, re.MULTILINE)
    if result.returncode or not match:
        raise RuntimeError(result.stdout + "\n" + result.stderr)
    return int(match[1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", action="store_true")
    parser.add_argument("--seconds", type=float, default=60)
    args = parser.parse_args()
    passed = 0
    with tempfile.TemporaryDirectory(prefix="exact_marginal_check_") as directory:
        path = Path(directory) / "case.cnf"
        for method in ["sequential", "network"]:
            for n in range(8):
                for target in range(n + 1):
                    cnf = CNF()
                    inputs = [cnf.variable() for _ in range(n)]
                    FunctionalGates(cnf).exactly(inputs, target, method)
                    write_cnf(path, cnf, {})
                    count = exact_count(path, args.seconds)
                    assert count == math.comb(n, target), (method, n, target, count)
                    passed += 1
            for target in range(3):
                cnf = CNF()
                x = cnf.variable()
                FunctionalGates(cnf).exactly([x, -x], target, method)
                write_cnf(path, cnf, {})
                count = exact_count(path, args.seconds)
                assert count == (2 if target == 1 else 0), (method, target, count)
                passed += 1
            for orbit, pairs, system in itertools.product(
                [False, True], [[], ["LM", "MR", "TM"]], ["roles", "boundary", "both"]
            ):
                cnf, cells, stats = make_marginal_cnf(
                    2,
                    [],
                    orbit_canonical=orbit,
                    cardinality=method,
                    pairs=pairs,
                    marginal_system=system,
                )
                write_cnf(path, cnf, cells)
                started = time.monotonic()
                count = exact_count(path, args.seconds)
                assert count == (42 if orbit else 168), (method, orbit, pairs, count)
                passed += 1
                print(
                    json.dumps(
                        {
                            "case": "binary",
                            "method": method,
                            "orbit": orbit,
                            "pairs": pairs,
                            "marginal_system": system,
                            "count": count,
                            "wall_seconds": round(time.monotonic() - started, 3),
                            "variables": stats["variables"],
                            "clauses": stats["clauses"],
                        }
                    ),
                    flush=True,
                )
            if args.prefix:
                data = json.loads((ROOT / "sources/anc/certificates.json").read_text())
                cnf, cells, stats = make_marginal_cnf(
                    3, data["ternary_prefixes"]["C"], cardinality=method
                )
                # The large benchmark uses the same count-preserving support
                # hint as the original prefix benchmark. Small checks above
                # count every auxiliary directly.
                write_cnf(path, cnf, cells, independent_support=True)
                started = time.monotonic()
                count = exact_count(path, args.seconds)
                assert count == 2, (method, count)
                passed += 1
                print(
                    json.dumps(
                        {
                            "case": "prefix C",
                            "method": method,
                            "count": count,
                            "wall_seconds": round(time.monotonic() - started, 3),
                            "variables": stats["variables"],
                            "clauses": stats["clauses"],
                        }
                    ),
                    flush=True,
                )
    print(json.dumps({"exact_count_checks_passed": passed}), flush=True)


if __name__ == "__main__":
    main()
