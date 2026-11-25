#!/usr/bin/env python3
"""Collect and independently audit the larger three-color T-board family.

The fixed-width flattened ternary words give an exact, injective integer key.
No search result is trusted: every symmetry image is checked geometrically.
The search's prefix-completeness claim is recorded, not independently proved.
"""

import hashlib
import json
import re
from collections import Counter
from itertools import pairwise, permutations, product
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
PATTERNS = Counter(dict.fromkeys(product(range(3), repeat=4), 1))


def read_json(relative):
    return json.loads((ROOT / relative).read_text())


def read_jsonl(relative):
    return [json.loads(line) for line in (ROOT / relative).read_text().splitlines()]


def orbit(rows):
    return {
        tuple(
            "".join(str(p[int(c)]) for c in (row[::-1] if reflected else row))
            for row in rows
        )
        for p in permutations(range(3))
        for reflected in (False, True)
    }


def verify_coordinates(rows):
    if len(rows) != 10 or any(len(row) != 2 * r + 1 for r, row in enumerate(rows)):
        raise ValueError("incorrect row lengths")
    if any(c not in "012" for row in rows for c in row):
        raise ValueError("invalid color")
    grid = {
        (j - r, -r): int(color)
        for r, row in enumerate(rows)
        for j, color in enumerate(row)
    }
    histogram = Counter()
    for x, y in grid:
        # The first point is directly above the middle of the horizontal triple.
        points = [(x, y + 1), (x - 1, y), (x, y), (x + 1, y)]
        if all(point in grid for point in points):
            histogram[tuple(grid[point] for point in points)] += 1
    if len(grid) != 100 or histogram != PATTERNS:
        raise ValueError("board fails exact-pattern geometric check")


def main():
    published = read_json("sources/anc/certificates.json")["ternary_seeds"]
    original = read_json("prefix_result.json")["rows"]
    prefix0 = read_jsonl("extended_prefix0.jsonl")
    prefix1 = read_jsonl("more_results.jsonl")
    records = [(rows, "published ternary_seeds", i) for i, rows in enumerate(published)]
    records += [(original, "prefix_result.json", 0)]
    records += [
        (record["rows"], "extended_prefix0.jsonl", i)
        for i, record in enumerate(prefix0)
    ]
    records += [
        (record["rows"], "more_results.jsonl", i) for i, record in enumerate(prefix1)
    ]
    representatives: list[dict[str, Any]] = []
    by_canonical = {}
    full = set()
    for rows, source, entry in records:
        variants = orbit(rows)
        if len(variants) != 12:
            raise ValueError(f"orbit is not of size12: {source}:{entry}")
        canonical = min("".join(board) for board in variants)
        provenance = {"source": source, "entry": entry}
        if canonical in by_canonical:
            representatives[by_canonical[canonical]]["provenance"].append(provenance)
            continue
        if variants & full:
            raise ValueError("unequal canonical keys for overlapping orbits")
        index = len(representatives)
        by_canonical[canonical] = index
        representatives.append(
            {
                "index": index,
                "rows": rows,
                "canonical_flat": canonical,
                "provenance": [provenance],
            }
        )
        full |= variants

    family = sorted(full, key=lambda board: "".join(board))
    numeric_keys = []
    for board in family:
        verify_coordinates(board)
        numeric_keys.append(int("".join(board), 3))
    if not all(a < b for a, b in pairwise(numeric_keys)):
        raise ValueError("base3 board keys are not strictly increasing")
    if len(family) != 12 * len(representatives):
        raise ValueError("incorrect orbit union cardinality")

    prefix0_summary = read_json("extended_prefix0_summary.json")
    prefix1_log = (ROOT / "more_search.log").read_text().splitlines()[-1]
    match = re.fullmatch(
        r"nodes=(\d+) leaves=(\d+) new_orbits=(\d+) exhaustive=(\d+) elapsed=([\d.]+)",
        prefix1_log,
    )
    if match is None:
        raise ValueError("missing or malformed final prefix1 search statistics")
    nodes, leaves, fresh, exhaustive, elapsed = match.groups()
    output_seeds = ROOT / "extended_seeds.json"
    output_family = ROOT / "extended_family.json"
    output_seeds.write_text(json.dumps(representatives, indent=2) + "\n")
    output_family.write_text(json.dumps(family, indent=2) + "\n")
    summary = {
        "input_representatives": len(records),
        "distinct_symmetry_orbits": len(representatives),
        "duplicate_orbit_inputs_removed": len(records) - len(representatives),
        "orbit_size": 12,
        "distinct_labelled_boards": len(family),
        "published_boards": 60,
        "additional_boards_beyond_publication": len(family) - 60,
        "sources": {
            "published_seed_count": len(published),
            "original_novel_seed_count": 1,
            "extended_prefix0_seed_count": len(prefix0),
            "more_results_seed_count": len(prefix1),
        },
        "validation": {
            "every_full_orbit_member_checked": True,
            "method": "independent Cartesian-coordinate enumeration of every translated T",
            "cells_per_board": 100,
            "placements_per_board": 81,
            "every_ordered_pattern_occurs_exactly_once": True,
            "family_order": "strictly increasing 100-digit flattened ternary integer",
            "lean_formalization": "not asserted by this Python collector",
        },
        "scope": {
            "global_result": "certified computational lower bound; exact unrestricted count not determined",
            "prefix0": {
                "fixed_upper_rows": prefix0_summary["prefix_rows"],
                "reported_exhaustive": prefix0_summary["exhaustive"],
                "completions": prefix0_summary["completions"],
                "completeness_lean_proved": False,
                "nodes": prefix0_summary["nodes"],
                "elapsed_seconds": prefix0_summary["elapsed_seconds"],
            },
            "prefix1": {
                "fixed_upper_rows": published[1][:6],
                "reported_exhaustive": bool(int(exhaustive)),
                "solution_leaves_before_timeout": int(leaves),
                "additional_orbits_before_timeout": int(fresh),
                "nodes": int(nodes),
                "elapsed_seconds": float(elapsed),
                "exact_prefix_count": None,
            },
        },
        "sha256": {
            path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (output_seeds, output_family)
        },
    }
    (ROOT / "extended_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(
        json.dumps(
            {
                "symmetry_orbits": len(representatives),
                "individually_verified_boards": len(family),
                "duplicate_inputs_removed": len(records) - len(representatives),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
