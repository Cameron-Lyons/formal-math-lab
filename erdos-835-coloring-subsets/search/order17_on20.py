"""Generate a DIMACS exact-cover problem for a cyclic quadruple seed on 20 points.

Variable i, starting at 1, selects the i-th eligible quadruple in lexicographic
order. Without --extend all quadruples are eligible. With a JSON list of fixed
blocks, omit those blocks and the quadruples incompatible with them.
"""

import argparse
from collections import defaultdict
from functools import cache
from itertools import combinations
import json
from pathlib import Path
import sys


@cache
def orbit_representative(block):
    return min(
        tuple(sorted((x + shift) % 17 if x < 17 else x for x in block))
        for shift in range(17)
    )


def incidences(block):
    return [*combinations(block, 3), orbit_representative(block)]


def read_blocks(path):
    data = json.loads(path.read_text())
    if not isinstance(data, list):
        raise ValueError("expected a JSON list of quadruples")
    blocks = []
    for row in data:
        if not isinstance(row, list) or len(row) != 4 or any(
            type(x) is not int or not 0 <= x < 20 for x in row
        ) or row != sorted(set(row)):
            raise ValueError(f"invalid quadruple: {row!r}")
        blocks.append(tuple(row))
    return blocks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extend", type=Path, help="JSON file of required quadruples")
    args = parser.parse_args()
    try:
        fixed = read_blocks(args.extend) if args.extend else []
    except (ValueError, OSError) as exc:
        parser.error(str(exc))

    used = {key for block in fixed for key in incidences(block)}
    if len(used) != 5 * len(fixed):
        parser.error("the required quadruples repeat a triple or a translation orbit")

    triples = {t: [] for t in combinations(range(20), 3) if t not in used}
    orbits = defaultdict(list)
    variables = 0
    for block in combinations(range(20), 4):
        orbit = orbit_representative(block)
        if orbit in used:
            continue
        group = orbits[orbit]
        faces = list(combinations(block, 3))
        if any(t in used for t in faces):
            continue
        variables += 1
        group.append(variables)
        for triple in faces:
            triples[triple].append(variables)

    assert len(triples) == 1140 - 4 * len(fixed) and len(orbits) == 285 - len(fixed)
    groups = [*triples.values(), *orbits.values()]
    clauses = sum(1 + len(g) * (len(g) - 1) // 2 for g in groups)
    print(f"p cnf {variables} {clauses}")
    for group in groups:
        print(*group, 0)
        for a, b in combinations(group, 2):
            sys.stdout.write(f"-{a} -{b} 0\n")


if __name__ == "__main__":
    main()
