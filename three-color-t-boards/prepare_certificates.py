"""Rebuild the explicit Lean data and an inverse-pattern certificate.

The original five seeds are Qiyuan Ma's CC-BY-4.0 certificate data,
https://doi.org/10.5281/zenodo.23631079. The sixth seed was found here.
This generator is not in the proof's trusted computing base.
"""

import csv
import itertools
import json
from pathlib import Path


def lean_board(rows):
    return "[\n" + ",\n".join("  [" + ",".join(row) + "]" for row in rows) + "\n]"


def main():
    published = json.loads(Path("sources/anc/certificates.json").read_text())[
        "ternary_seeds"
    ]
    novel = json.loads(Path("prefix_result.json").read_text())["rows"]
    seeds = [*published, novel]
    lines = [
        "import TBoards",
        "",
        "namespace TBoards",
        "",
        "/- Published seeds 0–4: Qiyuan Ma, DOI 10.5281/zenodo.23631079,",
        "   certificate data licensed CC-BY-4.0. Seed 5 is the new witness. -/",
        "",
    ]
    for i, rows in enumerate(seeds):
        lines += [f"def seed{i} : Board := {lean_board(rows)}", ""]
    lines += [
        "def publishedSeeds : List Board := [seed0, seed1, seed2, seed3, seed4]",
        "def novel : Board := seed5",
        "",
        "def colorPermutations : List (List Nat) :=",
        "  [[0,1,2], [0,2,1], [1,0,2], [1,2,0], [2,0,1], [2,1,0]]",
        "",
        "/-- Apply a global color permutation, optionally reflecting every row. -/",
        "def transform (b : Board) (perm : List Nat) (reflect : Bool) : Board :=",
        "  b.map fun row => (if reflect then row.reverse else row).map fun c => perm.getD c 0",
        "",
        "def orbit (b : Board) : List Board :=",
        "  colorPermutations.flatMap fun p => [transform b p false, transform b p true]",
        "",
        "def published : List Board := publishedSeeds.flatMap orbit",
        "def newOrbit : List Board := orbit novel",
        "def family : List Board := published ++ newOrbit",
        "",
        "end TBoards",
        "",
    ]
    Path("BoardData.lean").write_text("\n".join(lines))
    family = [
        ["".join(p[int(c)] for c in (row[::-1] if reverse else row)) for row in rows]
        for rows in seeds
        for p in itertools.permutations("012")
        for reverse in [False, True]
    ]
    if len(set(map(tuple, family))) != 72:
        raise ValueError("Family is not 72 distinct boards")
    Path("family.json").write_text(json.dumps(family, indent=2) + "\n")
    patterns = []
    for r in range(1, 10):
        for j in range(2 * r - 1):
            a, l, m, z = map(int, (novel[r - 1][j], *novel[r][j : j + 3]))
            patterns.append(
                (27 * a + 9 * l + 3 * m + z, a, l, m, z, r, j, j + 1 - r, -r)
            )
    if sorted(p[0] for p in patterns) != list(range(81)):
        raise ValueError("Invalid novel certificate")
    with Path("novel_patterns.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "code",
                "top",
                "left",
                "middle",
                "right",
                "lower_row",
                "lower_left_index",
                "center_x",
                "center_y",
            ]
        )
        writer.writerows(sorted(patterns))
    print(
        "Generated BoardData.lean, family.json (72 boards), novel_patterns.csv (81 patterns)."
    )


if __name__ == "__main__":
    main()
