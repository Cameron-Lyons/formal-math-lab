"""Replay the finite searches proving the Erdős–Gyárfás conjecture through 41."""

import argparse
import re
import subprocess
from pathlib import Path


def center_seeds():
    yield ["shared", 41, 20, 3, 0, 120_000]
    for degree in range(3, 21):
        for triangles in range(1, degree // 2 + 1):
            if 1 + 3 * degree - 2 * triangles <= 41:
                yield ["shared", 41, 20, degree, triangles, 120_000]


def replay(executable, cases, expected):
    total = 0
    for arguments in cases:
        command = [str(executable), *map(str, arguments)]
        output = subprocess.run(
            command, check=True, text=True, stdout=subprocess.PIPE
        ).stdout
        print(output, end="", flush=True)
        count = re.fullmatch(r"No candidate [^\n]+: (\d+) states\.\n?", output)
        if count is None:
            raise RuntimeError(f"Unexpected output from {' '.join(command)}")
        total += int(count[1])
    if total != expected:
        raise RuntimeError(f"Expected {expected:,} states, visited {total:,}")
    return total


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "checker", type=Path, help="root_degree_search built with USE_NAUTY"
    )
    parser.add_argument(
        "--split-adjacent",
        action="store_true",
        help="split adjacent triangles by a second path to visit fewer states",
    )
    args = parser.parse_args()
    checker = args.checker.resolve()
    center = replay(checker, center_seeds(), 31_203_215)
    pairs = replay(
        checker, (["pair", 41, 20, r, 3, 120_000] for r in range(2, 37)), 24_615_340
    )
    if args.split_adjacent:
        adjacent = replay(
            checker, (["ear", 41, 20, s, -1, 120_000] for s in range(1, 37)), 9_882_550
        )
    else:
        adjacent = replay(checker, [["pair", 41, 20, 1, 3, 180_000]], 32_800_764)
    print(f"All cases exhausted in {center + pairs + adjacent:,} states.")


if __name__ == "__main__":
    main()
