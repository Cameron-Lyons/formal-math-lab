#!/usr/bin/env python3
"""Exact local-permutation parametrization; exhaust the binary case only.

The ternary helper decodes a supplied parameter tuple; it does not exhaust
3^19 * 6^27 tuples or claim to have obtained the ternary count.
"""

import json
import sys
from itertools import permutations, product
from pathlib import Path


def decode(n, boundary, outputs):
    m = n * n
    assert len(boundary) == 2 * m + 1
    assert len(outputs) == n**3
    rows = [[boundary[0]]]
    used = [0] * (n**3)
    for r in range(1, m + 1):
        row = list(boundary[2 * r - 1 : 2 * r + 1])
        for j in range(2 * r - 1):
            triple = n * n * rows[-1][j] + n * row[j] + row[j + 1]
            if used[triple] == n:
                return None
            row.append(outputs[triple][used[triple]])
            used[triple] += 1
        rows.append(row)
    assert all(k == n for k in used)
    return tuple(tuple(row) for row in rows)


def encode(n, rows):
    assert len(rows) == n * n + 1
    boundary = [rows[0][0]]
    outputs = [[] for _ in range(n**3)]
    for r in range(1, len(rows)):
        boundary.extend(rows[r][:2])
        for j in range(2 * r - 1):
            triple = n * n * rows[r - 1][j] + n * rows[r][j] + rows[r][j + 1]
            outputs[triple].append(rows[r][j + 2])
    assert all(sorted(v) == list(range(n)) for v in outputs)
    return tuple(boundary), tuple(tuple(v) for v in outputs)


def independent_geometric_check(n, rows):
    cells = {(j - r, -r): c for r, row in enumerate(rows) for j, c in enumerate(row)}
    patterns = []
    for x, y in cells:
        coords = [(x, y + 1), (x - 1, y), (x, y), (x + 1, y)]
        if all(p in cells for p in coords):
            patterns.append(tuple(cells[p] for p in coords))
    assert len(patterns) == n**4
    assert set(patterns) == set(product(range(n), repeat=4))


def main():
    n = 2
    perms = tuple(permutations(range(n)))
    found = set()
    attempted = 0
    for boundary in product(range(n), repeat=2 * n * n + 1):
        for outputs in product(perms, repeat=n**3):
            attempted += 1
            rows = decode(n, boundary, outputs)
            if rows is None:
                continue
            independent_geometric_check(n, rows)
            assert encode(n, rows) == (boundary, outputs)
            assert rows not in found
            found.add(rows)
    assert len(found) == 168
    print(
        f"binary tuples={attempted}; accepted={len(found)}; independent geometry and round trips PASS"
    )

    source = Path(__file__).resolve().parents[1] / "sources" / "anc"
    sys.path.insert(0, str(source))
    from count_extensions import count_extensions

    previous, _, _ = count_extensions(2, [])
    flat_found = {bytes(c for row in rows for c in row) for rows in found}
    assert flat_found == set(previous)
    print("binary exact board set equals independent cell-by-cell enumeration PASS")

    seeds = json.loads((source / "certificates.json").read_text())["ternary_seeds"]
    for seed in seeds:
        rows = tuple(tuple(map(int, row)) for row in seed)
        boundary, outputs = encode(3, rows)
        assert decode(3, boundary, outputs) == rows
        independent_geometric_check(3, rows)
    print(
        f"ternary seed round trips={len(seeds)} PASS; unrestricted ternary count NOT COMPUTED"
    )


if __name__ == "__main__":
    main()
