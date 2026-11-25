"""Check the six-board proof using only Python's standard library.

Run `python simple_proof.py`; add `--codes` to reproduce the proof's code table,
or `--published` to compare with all 60 boards in the supplied source certificate.
The six suffixes are entries 841,842,843,845,846,849 of extended_seeds.json.
All data needed for the default check are included here; no search files are read.
"""

import json
import sys
from collections import Counter
from itertools import permutations, product
from pathlib import Path

PREFIX = (
    "0",
    "000",
    "21121",
    "2102221",
    "010122001",
    "22111212222",
    "0120111221110",
)
SUFFIXES = (
    ("001022002021212", "10110022000210001", "1202021011020120100"),
    ("002011000212101", "10202202100020012", "1200101102120220100"),
    ("100220200010002", "21202020101102101", "0210011022012002121"),
    ("101011000012120", "20200210220022010", "1001100202021021201"),
    ("201002000212101", "10110202100020220", "1001200102120220110"),
    ("212021210220200", "00021000100201101", "1022012020010110021"),
)
BOARDS = tuple(PREFIX + suffix for suffix in SUFFIXES)


def codes_by_row(rows):
    return [
        [
            27 * int(rows[r - 1][j])
            + 9 * int(rows[r][j])
            + 3 * int(rows[r][j + 1])
            + int(rows[r][j + 2])
            for j in range(2 * r - 1)
        ]
        for r in range(1, 10)
    ]


def verify(rows):
    if len(rows) != 10 or any(len(row) != 2 * r + 1 for r, row in enumerate(rows)):
        raise ValueError("incorrect row lengths")
    if any(c not in "012" for row in rows for c in row):
        raise ValueError("incorrect palette")
    if sorted(code for row in codes_by_row(rows) for code in row) != list(range(81)):
        raise ValueError("row-indexed check failed")

    # Independently enumerate all geometric translates, without the row formula.
    grid = {
        (j - r, -r): int(c) for r, row in enumerate(rows) for j, c in enumerate(row)
    }
    patterns = Counter()
    for x, y in grid:
        cells = ((x, y + 1), (x - 1, y), (x, y), (x + 1, y))
        if all(cell in grid for cell in cells):
            patterns[tuple(grid[cell] for cell in cells)] += 1
    if patterns != Counter(dict.fromkeys(product(range(3), repeat=4), 1)):
        raise ValueError("Cartesian-coordinate check failed")


def symmetry_images(rows):
    for p in permutations(range(3)):
        for reflected in (False, True):
            yield tuple(
                "".join(str(p[int(c)]) for c in (row[::-1] if reflected else row))
                for row in rows
            )


def compare_with_published(family):
    source = Path(__file__).resolve().parent / "sources/anc/certificates.json"
    seeds = json.loads(source.read_text())["ternary_seeds"]
    if len(seeds) != 5:
        raise ValueError("expected the five published representatives")
    published = set()
    for rows in seeds:
        verify(rows)
        published.update(symmetry_images(rows))
    if len(published) != 60:
        raise ValueError("published family does not contain 60 distinct boards")
    for board in published:
        verify(board)
    if family & published:
        raise ValueError("new family overlaps the published family")
    print(
        "Published comparison: all 60 boards valid; overlap 0; board A is outside all five families."
    )


def main():
    family = set()
    for rows in BOARDS:
        verify(rows)
        for board in symmetry_images(rows):
            verify(board)
            if board in family:
                raise ValueError("two symmetry images coincide")
            family.add(board)
    if len(family) != 72:
        raise ValueError("incorrect family size")
    print(
        "Verified: 6 representatives, 72 distinct valid boards, 81 patterns per board."
    )
    if "--published" in sys.argv[1:]:
        compare_with_published(family)
    if "--codes" in sys.argv[1:]:
        print("\nShared rows:")
        for r, codes in enumerate(codes_by_row(BOARDS[0])[:6], 1):
            print(f"  {r}: " + " ".join(f"{code:02}" for code in codes))
        for name, rows in zip("ABCDEF", BOARDS, strict=False):
            print(f"{name}:")
            for r, codes in enumerate(codes_by_row(rows)[6:], 7):
                print(f"  {r}: " + " ".join(f"{code:02}" for code in codes))


if __name__ == "__main__":
    main()
