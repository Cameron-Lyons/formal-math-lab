#!/usr/bin/env python3
import argparse
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--groups", default="1")
    p.add_argument("--depths", default="0,4,8,17")
    p.add_argument("--capacity", type=int, default=1000000)
    p.add_argument("--timeout", type=float, default=120)
    p.add_argument(
        "--output", type=Path, default=ROOT / "experiments/exact_lastrow_benchmark.json"
    )
    a = p.parse_args()
    groups = json.loads((ROOT / "splice_witnesses.json").read_text())["groups"]
    results = []
    with tempfile.TemporaryDirectory(prefix="tboards-lastrow-benchmark-") as tmp:
        binary = Path(tmp) / "counter"
        subprocess.run(
            [
                "g++",
                "-O3",
                "-std=c++23",
                "-Wall",
                "-Wextra",
                "-Wpedantic",
                "-Werror",
                str(ROOT / "experiments/exact_lastrow_search.cpp"),
                "-o",
                str(binary),
            ],
            check=True,
        )
        for group in map(int, a.groups.split(",")):
            source = groups[group - 1]
            prefix = source["prefix"]
            expected = len(source["tails"])
            for depth in map(int, a.depths.split(",")):
                args = [str(binary), prefix, str(depth), str(a.capacity)]
                r = subprocess.run(
                    args, text=True, capture_output=True, timeout=a.timeout, check=True
                )
                lines = [
                    dict(t.split("=", 1) for t in line.split())
                    for line in r.stdout.splitlines()
                ]
                assert (
                    lines[0]["status"] == "COMPLETE"
                    and int(lines[0]["count"]) == expected
                )
                record = {
                    "group": group,
                    "arguments": args[1:],
                    "summary": lines[0],
                    "depth_stats": lines[1:],
                }
                results.append(record)
                a.output.write_text(json.dumps(results, indent=2) + "\n")
                print("group", group, r.stdout, flush=True)


if __name__ == "__main__":
    main()
