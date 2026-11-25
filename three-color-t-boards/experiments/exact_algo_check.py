#!/usr/bin/env python3
"""Independent small-instance, partition, and timeout checks of exact counter."""

import itertools
import json
import subprocess
import tempfile
from pathlib import Path

from exact_algo_census import ROOT, count, independent_patterns, prefix_orbits


def main():
    with tempfile.TemporaryDirectory(prefix="tboards-exact-check-") as directory:
        binary = Path(directory) / "count"
        subprocess.run(
            [
                "g++",
                "-O3",
                "-std=c++23",
                "-Wall",
                "-Wextra",
                "-Wpedantic",
                "-Werror",
                str(ROOT / "experiments/exact_algo_count.cpp"),
                "-o",
                str(binary),
            ],
            check=True,
        )
        fixed_binary = Path(directory) / "fixed"
        subprocess.run(
            [
                "g++",
                "-O3",
                "-std=c++23",
                "-Wall",
                "-Wextra",
                "-Wpedantic",
                "-Werror",
                str(ROOT / "experiments/exact_algo_fixed.cpp"),
                "-o",
                str(fixed_binary),
            ],
            check=True,
        )
        for q, rows in ((2, 3), (2, 4), (3, 3)):
            expected = 0
            fixed = [0, 0]
            for digits in itertools.product(range(q), repeat=rows * rows):
                word = "".join(map(str, digits))
                patterns = independent_patterns(word, q, rows)
                valid = len(set(patterns)) == len(patterns)
                expected += valid
                if q == 3 and rows == 3 and valid:
                    reflected = "".join(
                        word[r * r : (r + 1) ** 2][::-1] for r in range(rows)
                    )
                    fixed[0] += word == reflected
                    fixed[1] += word == reflected.translate(str.maketrans("012", "021"))
            actual, _ = count(binary, q, rows, "")
            assert actual == expected
            print(f"coordinate brute force: colors={q} rows={rows} count={actual} PASS")
            if q == 3 and rows == 3:
                run = subprocess.run(
                    [str(fixed_binary), "3", "3"],
                    text=True,
                    capture_output=True,
                    check=True,
                )
                actual_fixed = [
                    int(line.split("fixed=")[1]) for line in run.stdout.splitlines()
                ]
                assert fixed == actual_fixed == [468, 18]
                print(
                    "reflection fixed-point counter agrees with coordinate brute force PASS"
                )
        assert count(binary, 2, 5, "")[0] == 168
        print("unrestricted binary complete count=168 PASS")
        for q, rows, expected in ((2, 5, 168), (3, 3, 18342)):
            total = sum(
                count(binary, q, rows, "".join(map(str, prefix)))[0]
                for prefix in itertools.product(range(q), repeat=4)
            )
            assert total == expected
            print(f"all {q**4} first-two-row prefix shards sum to {total} PASS")
        groups, rejected = prefix_orbits(3, 3)
        assert len(groups) == 1572 and rejected == 1341
        assert sum(groups.values()) == 18342
        assert sorted(groups.values()).count(6) == 87
        assert sorted(groups.values()).count(12) == 1485
        print(
            "prefix orbit images checked independently: 87 of size6, 1485 of size12 PASS"
        )
        assert count(binary, 3, 5, "000000000")[0] == 0
        print("prefix with repeated T pattern has no completions PASS")
        certificates = json.loads((ROOT / "sources/anc/certificates.json").read_text())
        for name, rows in certificates["ternary_prefixes"].items():
            actual, stats = count(binary, 3, 10, "".join(rows), seconds=10)
            assert stats["status"] == "COMPLETE" and actual == 2
            print(f"published seven-row ternary prefix {name}: exact count=2 PASS")
        for rows in certificates["ternary_seeds"]:
            assert count(binary, 3, 10, "".join(rows))[0] == 1
        print(
            "all five completely fixed 100-cell ternary boards count exactly once PASS"
        )
        run = subprocess.run(
            [
                str(binary),
                "--colors",
                "3",
                "--rows",
                "5",
                "--split-cells",
                "9",
                "--begin",
                "205",
                "--end",
                "207",
                "--seconds",
                "0.000001",
            ],
            text=True,
            capture_output=True,
            check=False,
        )
        fields = dict(x.split("=", 1) for x in run.stdout.strip().split())
        assert run.returncode == 1 and fields["status"] == "INCOMPLETE"
        assert fields["completed_end"] == "205"
        assert fields["exact_count_completed_interval"] == "0"
        print("timeout discards unfinished shard and reports resumable boundary PASS")


if __name__ == "__main__":
    main()
