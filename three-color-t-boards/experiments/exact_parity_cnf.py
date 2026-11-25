#!/usr/bin/env python3
"""Exact T-board model from odd occurrence counts, with functional XOR gates.

There are q^4 placements and q^4 patterns. If every nonnegative pattern
count is odd, each is at least one, so their fixed total forces all to one.
The converse is immediate. No per-pattern OR or at-most-one is required.
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path

from exact_count_cnf import CNF, add_palette_normalization, add_reflection_normalization
from exact_marginal_cnf import FunctionalGates, negate


class ParityCNF(CNF):
    def __init__(self):
        super().__init__()
        self.native_xors: list[tuple[list[int], bool]] = []


class ParityGates(FunctionalGates):
    def __init__(self, cnf):
        super().__init__(cnf)
        if not hasattr(cnf, "native_xors"):
            cnf.native_xors = []

    def xor_gate(self, a, b):
        if isinstance(a, bool):
            return negate(b) if a else b
        if isinstance(b, bool):
            return negate(a) if b else a
        if a == b:
            return False
        if a == -b:
            return True
        a, b = sorted((a, b))
        key = ("xor", a, b)
        if key not in self.cache:
            z = self.cnf.variable()
            self.cache[key] = z
            # z iff a XOR b: all four forbidden triples are excluded.
            self.clause([a, b, -z])
            self.clause([-a, -b, -z])
            self.clause([a, -b, z])
            self.clause([-a, b, z])
        return self.cache[key]

    def require_xor(self, literals, rhs=True, layout="chain"):
        # Cancel constants, repeated variables and literal signs over F_2.
        variables = Counter()
        for literal in literals:
            if isinstance(literal, bool):
                rhs ^= literal
            else:
                rhs ^= literal < 0
                variables[abs(literal)] += 1
        row = sorted(v for v, multiplicity in variables.items() if multiplicity % 2)
        if not row:
            if rhs:
                self.cnf.add([])
            return
        if len(row) == 1:
            self.clause([row[0] if rhs else -row[0]])
            return
        if layout == "native":
            self.cnf.native_xors.append((row, bool(rhs)))
            return
        if layout == "chain":
            value = row[0]
            for literal in row[1:]:
                value = self.xor_gate(value, literal)
        elif layout == "tree":
            while len(row) > 1:
                row = [
                    self.xor_gate(row[i], row[i + 1]) for i in range(0, len(row) - 1, 2)
                ] + ([row[-1]] if len(row) % 2 else [])
            value = row[0]
        else:
            raise ValueError(layout)
        self.clause([value if rhs else negate(value)])


def make_parity_cnf(
    colors,
    prefix=(),
    canonical=False,
    orbit_canonical=False,
    layout="chain",
    connected=False,
):
    if colors not in (1, 2, 3) or layout not in ("chain", "tree", "native"):
        raise ValueError("invalid palette or XOR layout")
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
    cnf = ParityCNF()
    cells = {
        pos: [cnf.variable() for _ in range(colors)]
        for pos in range(len(fixed), height * height)
    }
    for indicators in cells.values():
        cnf.add(indicators)
        for a, b in itertools.combinations(indicators, 2):
            cnf.add([-a, -b])
    gates = ParityGates(cnf)
    windows = [
        ((r - 1) ** 2 + j, r * r + j, r * r + j + 1, r * r + j + 2)
        for r in range(1, height)
        for j in range(2 * r - 1)
    ]
    occurrence_gates = 0
    xor_gates = 0
    by_window = [[] for _ in windows]
    for pattern in itertools.product(range(colors), repeat=4):
        occurrences = []
        for window_index, window in enumerate(windows):
            if any(
                pos < len(fixed) and fixed[pos] != color
                for pos, color in zip(window, pattern, strict=False)
            ):
                continue
            inputs = [
                cells[pos][color]
                for pos, color in zip(window, pattern, strict=False)
                if pos >= len(fixed)
            ]
            if not inputs:
                occurrence = True
            elif len(inputs) == 1:
                occurrence = inputs[0]
            else:
                occurrence = cnf.conjunction(inputs)
                occurrence_gates += 1
            occurrences.append(occurrence)
            by_window[window_index].append(occurrence)
        before = cnf.variables
        gates.require_xor(occurrences, True, layout)
        xor_gates += cnf.variables - before
    redundant_parities = 0
    if connected:
        before = cnf.variables
        # Each placement realizes exactly one pattern. Reusing its occurrence
        # indicators connects the otherwise disjoint per-pattern XOR equations.
        for row in by_window:
            gates.require_xor(row, True, layout)
            redundant_parities += 1
        # Every role uses each color q^3 times in a valid board. The omitted
        # color's parity follows from one-hot cells and the total q^4.
        for role, color in itertools.product(range(4), range(colors - 1)):
            row = [
                fixed[window[role]] == color
                if window[role] < len(fixed)
                else cells[window[role]][color]
                for window in windows
            ]
            gates.require_xor(row, bool(colors**3 % 2), layout)
            redundant_parities += 1
        xor_gates += cnf.variables - before
    if canonical:
        add_palette_normalization(cnf, cells, colors)
    if orbit_canonical:
        add_reflection_normalization(cnf, cells, colors)
    stats = {
        "colors": colors,
        "prefix": list(prefix),
        "palette_canonical": canonical,
        "orbit_canonical": orbit_canonical,
        "xor_layout": layout,
        "windows": len(windows),
        "parity_constraints": colors**4,
        "connected_parities": connected,
        "redundant_parities": redundant_parities,
        "occurrence_gates": occurrence_gates,
        "xor_gates": xor_gates,
        "native_xor_equations": len(cnf.native_xors),
        "variables": cnf.variables,
        "clauses": len(cnf.clauses),
        "all_auxiliaries_functional": True,
    }
    return cnf, cells, stats


def rephase_parity(cnf, cells, board):
    from exact_phase import board_model, rephase

    assignment = board_model(cnf, cells, board)
    for variables, rhs in cnf.native_xors:
        if bool(sum(assignment[v] for v in variables) % 2) != rhs:
            raise ValueError(
                "supplied board does not satisfy the native parity constraints"
            )
    result = rephase(cnf, assignment)
    result.native_xors = [
        (variables, rhs ^ bool(sum(assignment[v] for v in variables) % 2))
        for variables, rhs in cnf.native_xors
    ]
    assert all(not rhs for _, rhs in result.native_xors)
    return result


def write_parity(path, cnf, cells, independent_support=False, comments=()):
    native = getattr(cnf, "native_xors", [])
    with Path(path).open("w") as file:
        file.write(
            "c Exact odd-pattern-count model; all auxiliary variables are functional.\n"
        )
        file.writelines("c " + comment + "\n" for comment in comments)
        if independent_support:
            support = [v for indicators in cells.values() for v in indicators[:-1]]
            file.write("c ind " + " ".join(map(str, support)) + " 0\n")
        file.write(f"p cnf {cnf.variables} {len(cnf.clauses) + len(native)}\n")
        file.writelines(" ".join(map(str, clause)) + " 0\n" for clause in cnf.clauses)
        for variables, rhs in native:
            # CryptoMiniSat x-lines require XOR(signed literals)=true.
            row = list(variables)
            if not rhs:
                row[0] = -row[0]
            file.write("x" + " ".join(map(str, row)) + " 0\n")


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
        "--layout", choices=("chain", "tree", "native"), default="chain"
    )
    parser.add_argument(
        "--connected",
        action="store_true",
        help="Add per-window and unary role/color parity equations.",
    )
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
    cnf, cells, stats = make_parity_cnf(
        args.colors,
        prefix,
        args.palette_canonical,
        args.orbit_canonical,
        args.layout,
        args.connected,
    )
    if args.phase_seed is not None:
        from exact_phase import default_board, normalize_board

        mode = (
            "orbit"
            if args.orbit_canonical
            else ("palette" if args.palette_canonical else "none")
        )
        board = normalize_board(
            default_board(args.colors, args.phase_seed), args.colors, mode
        )
        if board[: len(prefix)] != prefix:
            parser.error("phase witness does not extend the prefix")
        cnf = rephase_parity(cnf, cells, board)
        stats.update(
            phase_seed=args.phase_seed, phase_board=board, all_false_verified=True
        )
    write_parity(args.output, cnf, cells, args.independent_support, [json.dumps(stats)])
    Path(str(args.output) + ".json").write_text(json.dumps(stats, indent=2) + "\n")
    print(json.dumps(stats))


if __name__ == "__main__":
    main()
