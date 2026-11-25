#!/usr/bin/env python3
"""Exact T-board counting from a reduced, triangular system of pattern counts.

Fix (q-1)^4 pattern counts to one, and q^3+(q-1)q^2+(q-1)^2q+(q-1)^3
selected triple marginals to q. Induction on coordinates equal to q-1 then
forces every q^4 pattern count to one. All auxiliary gates are functional.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from exact_count_cnf import CNF, add_palette_normalization, add_reflection_normalization
from exact_marginal_cnf import FunctionalGates, write_cnf


def selected_lines(colors, drop_one_line=False):
    for omit in range(4):
        axes = tuple(i for i in range(4) if i != omit)
        domains = [range(colors - 1 if i < omit else colors) for i in axes]
        for values in itertools.product(*domains):
            # All omitted-axis-zero lines partition the entire pattern table.
            # Its total is q^4, so the final line follows from the other q^3-1.
            if drop_one_line and omit == 0 and values == (colors - 1,) * 3:
                continue
            yield omit, axes, values


def exact_occurrences(cnf, gates, literals, target, cardinality):
    target -= sum(x is True for x in literals)
    literals = [x for x in literals if not isinstance(x, bool)]
    if target == 1 and literals:
        cnf.add(literals)
        cnf.at_most_one(literals, "tree")
    else:
        gates.exactly(literals, target, cardinality)


def make_reduced_cnf(
    colors,
    prefix=(),
    canonical=False,
    orbit_canonical=False,
    cardinality="sequential",
    drop_one_line=False,
):
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
    for indicators in cells.values():
        cnf.add(indicators)
        for a, b in itertools.combinations(indicators, 2):
            cnf.add([-a, -b])
    gates = FunctionalGates(cnf)
    windows = [
        ((r - 1) ** 2 + j, r * r + j, r * r + j + 1, r * r + j + 2)
        for r in range(1, height)
        for j in range(2 * r - 1)
    ]

    def indicator(pos, color):
        return fixed[pos] == color if pos < len(fixed) else cells[pos][color]

    def occurrence(window, axes, values):
        literal = True
        for axis, color in zip(axes, values, strict=False):
            literal = gates.and_gate(literal, indicator(window[axis], color))
        return literal

    lines = list(selected_lines(colors, drop_one_line))
    for _, axes, values in lines:
        exact_occurrences(
            cnf,
            gates,
            [occurrence(w, axes, values) for w in windows],
            colors,
            cardinality,
        )
    bases = list(itertools.product(range(colors - 1), repeat=4))
    for pattern in bases:
        # Reuse the lower-triple conjunctions already built for omitted axis 0.
        literals = [
            gates.and_gate(
                occurrence(w, (1, 2, 3), pattern[1:]), indicator(w[0], pattern[0])
            )
            for w in windows
        ]
        exact_occurrences(cnf, gates, literals, 1, cardinality)
    if canonical:
        add_palette_normalization(cnf, cells, colors)
    if orbit_canonical:
        add_reflection_normalization(cnf, cells, colors)
    stats = {
        "colors": colors,
        "prefix": list(prefix),
        "palette_canonical": canonical,
        "orbit_canonical": orbit_canonical,
        "cardinality": cardinality,
        "drop_one_line": drop_one_line,
        "quadruple_constraints": len(bases),
        "triple_constraints": len(lines),
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
    parser.add_argument(
        "--cardinality", choices=("sequential", "network"), default="sequential"
    )
    parser.add_argument("--drop-one-line", action="store_true")
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
    cnf, cells, stats = make_reduced_cnf(
        args.colors,
        prefix,
        args.palette_canonical,
        args.orbit_canonical,
        args.cardinality,
        args.drop_one_line,
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
