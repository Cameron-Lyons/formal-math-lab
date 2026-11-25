#!/usr/bin/env python3
"""Parsimonious exact model using pairwise inequality of the T windows.

A shared functional variable E(i,j) states that two cells have equal colors.
Each pair of windows contributes a clause saying that some role differs.
There are q^4 windows and q^4 patterns, so pairwise inequality is validity.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from exact_count_cnf import CNF, add_palette_normalization, add_reflection_normalization
from exact_marginal_cnf import FunctionalGates, negate, write_cnf


def make_compare_cnf(colors, prefix=(), canonical=False, orbit_canonical=False):
    if colors not in (1, 2, 3):
        raise ValueError("supported palettes have 1, 2, or 3 colors")
    height = colors * colors + 1
    if len(prefix) > height or any(
        len(row) != 2 * r + 1 for r, row in enumerate(prefix)
    ):
        raise ValueError("invalid prefix row lengths")
    if any(c not in "012"[:colors] for row in prefix for c in row):
        raise ValueError("prefix color outside palette")
    canonical = canonical or orbit_canonical
    if canonical and prefix:
        raise ValueError("symmetry normalization requires an unrestricted board")
    fixed = [int(c) for row in prefix for c in row]
    cnf = CNF()
    cells = {
        pos: [cnf.variable() for _ in range(colors)]
        for pos in range(len(fixed), height * height)
    }
    for variables in cells.values():
        cnf.add(variables)
        for a, b in itertools.combinations(variables, 2):
            cnf.add([-a, -b])
    gates = FunctionalGates(cnf)
    equalities = {}

    def equal(a, b):
        if a == b:
            return True
        a, b = sorted((a, b))
        if b < len(fixed):
            return fixed[a] == fixed[b]
        if a < len(fixed):
            return cells[b][fixed[a]]
        pair = a, b
        if pair not in equalities:
            e = cnf.variable()
            equalities[pair] = e
            # Exactly one (x,y) pair is active. Its clause fixes e uniquely.
            for x, y in itertools.product(range(colors), repeat=2):
                cnf.add([-cells[a][x], -cells[b][y], e if x == y else -e])
        return equalities[pair]

    windows = [
        ((r - 1) ** 2 + j, r * r + j, r * r + j + 1, r * r + j + 2)
        for r in range(1, height)
        for j in range(2 * r - 1)
    ]
    for first, second in itertools.combinations(windows, 2):
        # A known unequal coordinate makes this comparison vacuous; do not
        # introduce equalities for its other coordinates.
        if any(
            a < len(fixed) and b < len(fixed) and fixed[a] != fixed[b]
            for a, b in zip(first, second, strict=False)
        ):
            continue
        gates.clause([negate(equal(a, b)) for a, b in zip(first, second, strict=False)])
    if canonical:
        add_palette_normalization(cnf, cells, colors)
    if orbit_canonical:
        add_reflection_normalization(cnf, cells, colors)
    stats = {
        "colors": colors,
        "prefix": list(prefix),
        "palette_canonical": canonical,
        "orbit_canonical": orbit_canonical,
        "windows": len(windows),
        "window_pairs": len(windows) * (len(windows) - 1) // 2,
        "shared_equalities": len(equalities),
        "variables": cnf.variables,
        "clauses": len(cnf.clauses),
    }
    return cnf, cells, stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--colors", type=int, choices=(1, 2, 3), default=3)
    parser.add_argument("--prefix-json", type=Path)
    parser.add_argument("--prefix-name", choices=("C", "P"))
    parser.add_argument("--prefix-rows", type=int, default=6)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--orbit-canonical", action="store_true")
    parser.add_argument("--palette-canonical", action="store_true")
    parser.add_argument("--independent-support", action="store_true")
    parser.add_argument("--phase-seed", type=int)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if args.prefix_rows < 0 or (args.prefix_name and not args.prefix_json):
        parser.error("invalid fixed-prefix options")
    prefix = []
    if args.prefix_json:
        data = json.loads(args.prefix_json.read_text())
        if isinstance(data, dict):
            data = (
                data["ternary_prefixes"][args.prefix_name]
                if args.prefix_name
                else data["ternary_seeds"][args.seed]
            )
        prefix = data if args.prefix_name else data[: args.prefix_rows]
    cnf, cells, stats = make_compare_cnf(
        args.colors, prefix, args.palette_canonical, args.orbit_canonical
    )
    if args.phase_seed is not None:
        from exact_phase import board_model, default_board, normalize_board, rephase

        mode = (
            "orbit"
            if args.orbit_canonical
            else ("palette" if args.palette_canonical else "none")
        )
        board = normalize_board(
            default_board(args.colors, args.phase_seed), args.colors, mode
        )
        if board[: len(prefix)] != prefix:
            parser.error("phase witness does not extend the fixed prefix")
        assignment = board_model(cnf, cells, board)
        cnf = rephase(cnf, assignment)
        stats.update(
            {
                "phase_seed": args.phase_seed,
                "phase_board": board,
                "all_false_verified": True,
                "complemented": sum(assignment[1:]),
            }
        )
    write_cnf(args.output, cnf, cells, args.independent_support, [json.dumps(stats)])
    Path(str(args.output) + ".json").write_text(json.dumps(stats, indent=2) + "\n")
    print(json.dumps(stats))


if __name__ == "__main__":
    main()
