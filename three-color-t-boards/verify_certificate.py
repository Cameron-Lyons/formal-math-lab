"""Independent coordinate audit of the newly discovered certificate.

Uses Cartesian coordinates rather than flattened row-window indices.
"""
import itertools
import json
from collections import Counter
from pathlib import Path


def audit(rows):
    if len(rows) != 10 or any(len(row) != 2 * r + 1 for r, row in enumerate(rows)):
        raise ValueError("wrong geometry")
    grid = {(j - r, -r): int(color)
            for r, row in enumerate(rows) for j, color in enumerate(row)}
    if set(grid.values()) != {0, 1, 2}:
        raise ValueError("wrong colors")
    counts = Counter()
    for x, y in grid:
        t = [(x, y + 1), (x - 1, y), (x, y), (x + 1, y)]
        if all(cell in grid for cell in t):
            counts[tuple(grid[cell] for cell in t)] += 1
    target = Counter({p: 1 for p in itertools.product(range(3), repeat=4)})
    if counts != target:
        raise ValueError("patterns do not occur exactly once")
    return len(grid), sum(counts.values())


def orbit(rows):
    return {tuple("".join(str(p[int(c)]) for c in (row[::-1] if reverse else row))
                  for row in rows)
            for p in itertools.permutations(range(3)) for reverse in [False, True]}


def main():
    published = json.loads(Path("sources/anc/certificates.json").read_text())["ternary_seeds"]
    novel = json.loads(Path("prefix_result.json").read_text())["rows"]
    old = set().union(*(orbit(rows) for rows in published))
    new = orbit(novel)
    if len(old) != 60 or len(new) != 12 or old & new:
        raise ValueError("orbit cardinality/disjointness failure")
    for rows in old | new:
        if audit(rows) != (100, 81):
            raise ValueError("incorrect counts")
    print(json.dumps({"published": len(old), "new_orbit": len(new),
                      "intersection": len(old & new), "valid_distinct_total": len(old | new)}, indent=2))


if __name__ == "__main__":
    main()
