"""Independently audit all extra prefix-search witnesses and their full orbits."""
from collections import Counter
from itertools import permutations, product
import json
from pathlib import Path


def orbit(rows):
    return {
        tuple("".join(str(p[int(c)]) for c in (row[::-1] if reverse else row))
              for row in rows)
        for p in permutations(range(3)) for reverse in [False, True]
    }


def valid(rows):
    if len(rows) != 10 or any(len(row) != 2 * r + 1 for r, row in enumerate(rows)):
        raise ValueError("wrong shape")
    if any(c not in "012" for row in rows for c in row):
        raise ValueError("wrong color")
    grid = {(j - r, -r): int(c) for r, row in enumerate(rows) for j, c in enumerate(row)}
    histogram = Counter()
    for x, y in grid:
        cells = [(x, y + 1), (x - 1, y), (x, y), (x + 1, y)]
        if all(q in grid for q in cells):
            histogram[tuple(grid[q] for q in cells)] += 1
    if histogram != Counter({p: 1 for p in product(range(3), repeat=4)}):
        raise ValueError("incorrect pattern counts")


def main():
    published = json.loads(Path("sources/anc/certificates.json").read_text())["ternary_seeds"]
    first = json.loads(Path("prefix_result.json").read_text())["rows"]
    known = set().union(*(orbit(rows) for rows in published + [first]))
    if len(known) != 72:
        raise ValueError("incorrect prior family")
    extra = [json.loads(line)["rows"] for line in Path("more_results.jsonl").read_text().splitlines()]
    union = known.copy()
    for rows in extra:
        new = orbit(rows)
        if len(new) != 12 or new & union:
            raise ValueError("orbit size or overlap failure")
        union |= new
    for rows in union:
        valid(rows)
    print(json.dumps({"previous_boards": len(known), "additional_orbits": len(extra),
                      "additional_boards": len(union) - len(known),
                      "total_individually_verified_boards": len(union)}, indent=2))


if __name__ == "__main__":
    main()
