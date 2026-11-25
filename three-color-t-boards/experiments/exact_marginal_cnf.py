#!/usr/bin/env python3
"""Strengthen exact T-board CNF with functional exact marginal counters.

Every added constraint is implied by coverage of all ordered T patterns.
Every auxiliary is defined by a biconditional, preserving ordinary #SAT counts.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from exact_count_cnf import make_cnf

ROLE_NAMES = "TLMR"


def negate(literal):
    return not literal if isinstance(literal, bool) else -literal


class FunctionalGates:
    def __init__(self, cnf):
        self.cnf = cnf
        self.cache = {}

    def clause(self, literals):
        if any(x is True for x in literals):
            return
        values = {x for x in literals if x is not False}
        if any(-x in values for x in values):
            return
        self.cnf.add(sorted(values))

    def combine(self, a, b, conjunction):
        if a is (not conjunction) or b is (not conjunction):
            return not conjunction
        if a is conjunction:
            return b
        if b is conjunction:
            return a
        if a == b:
            return a
        if a == -b:
            return not conjunction
        a, b = sorted((a, b))
        key = ("and" if conjunction else "or", a, b)
        if key in self.cache:
            return self.cache[key]
        result = self.cnf.variable()
        self.cache[key] = result
        if conjunction:
            self.clause([-result, a])
            self.clause([-result, b])
            self.clause([result, -a, -b])
        else:
            self.clause([result, -a])
            self.clause([result, -b])
            self.clause([-result, a, b])
        return result

    def and_gate(self, a, b):
        return self.combine(a, b, True)

    def or_gate(self, a, b):
        return self.combine(a, b, False)

    def or_and(self, a, b, x):
        """A fresh, fully defined literal for a OR (b AND x)."""
        if b is False or x is False:
            return a
        if b is True:
            return self.or_gate(a, x)
        if x is True:
            return self.or_gate(a, b)
        if a is False:
            return self.and_gate(b, x)
        if a is True:
            return True
        if a in (b, x):
            return a
        if b == x:
            return self.or_gate(a, b)
        if b == -x:
            return a
        b, x = sorted((b, x))
        key = ("or_and", a, b, x)
        if key in self.cache:
            return self.cache[key]
        result = self.cnf.variable()
        self.cache[key] = result
        self.clause([-a, result])
        self.clause([-b, -x, result])
        self.clause([-result, a, b])
        self.clause([-result, a, x])
        return result

    def exactly(self, literals, target, method):
        target -= sum(x is True for x in literals)
        literals = [x for x in literals if not isinstance(x, bool)]
        if target < 0 or target > len(literals):
            self.cnf.add([])
            return
        if target == 0 or target == len(literals):
            for x in literals:
                self.clause([x if target else -x])
            return
        # Complementing keeps the sequential counter narrow, and is harmless
        # for the sorting network. All input variables retain unique meanings.
        if target > len(literals) // 2:
            literals = [-x for x in literals]
            target = len(literals) - target
        if method == "sequential":
            previous = [True] + [False] * (target + 1)
            for x in literals:
                previous = [True] + [
                    self.or_and(previous[k], previous[k - 1], x)
                    for k in range(1, target + 2)
                ]
            self.clause([previous[target]])
            self.clause([negate(previous[target + 1])])
        elif method == "network":
            size = 1 << (len(literals) - 1).bit_length()
            values = literals + [False] * (size - len(literals))

            def compare(i, j):
                a, b = values[i], values[j]
                values[i], values[j] = self.or_gate(a, b), self.and_gate(a, b)

            def merge(start, length, stride):
                step = stride * 2
                if step < length:
                    merge(start, length, step)
                    merge(start + stride, length, step)
                    for i in range(start + stride, start + length - stride, step):
                        compare(i, i + stride)
                else:
                    compare(start, start + stride)

            def sort(start, length):
                if length > 1:
                    half = length // 2
                    sort(start, half)
                    sort(start + half, half)
                    merge(start, length, 1)

            sort(0, size)
            self.clause([values[target - 1]])
            self.clause([negate(values[target])])
        else:
            raise ValueError(method)


def make_marginal_cnf(
    colors,
    prefix,
    canonical=False,
    occurrence_amo="tree",
    orbit_canonical=False,
    cardinality="network",
    roles=ROLE_NAMES,
    pairs=(),
    all_colors=True,
    marginal_system="roles",
):
    if marginal_system not in ("roles", "boundary", "both"):
        raise ValueError(marginal_system)
    if marginal_system != "roles" and roles != ROLE_NAMES:
        raise ValueError("boundary system uses all four roles; leave --roles as TLMR")
    cnf, cells = make_cnf(colors, prefix, canonical, occurrence_amo, orbit_canonical)
    before_vars, before_clauses = cnf.variables, len(cnf.clauses)
    gates = FunctionalGates(cnf)
    fixed = [int(c) for row in prefix for c in row]
    height = colors * colors + 1
    windows = [
        ((r - 1) ** 2 + j, r * r + j, r * r + j + 1, r * r + j + 2)
        for r in range(1, height)
        for j in range(2 * r - 1)
    ]

    def indicator(pos, color):
        return fixed[pos] == color if pos < len(fixed) else cells[pos][color]

    constraints = 0
    role_sets = {
        role: {w[index] for w in windows} for index, role in enumerate(ROLE_NAMES)
    }
    for role in "T" if marginal_system == "boundary" else roles:
        index = ROLE_NAMES.index(role)
        positions = [window[index] for window in windows]
        if len(set(positions)) != colors**4:
            raise AssertionError("role marginal requires distinct cell positions")
        for color in range(colors if all_colors else colors - 1):
            gates.exactly(
                [indicator(pos, color) for pos in positions], colors**3, cardinality
            )
            constraints += 1
    if marginal_system in ("boundary", "both"):
        for left, right in itertools.pairwise(ROLE_NAMES):
            left_only = sorted(role_sets[left] - role_sets[right])
            right_only = sorted(role_sets[right] - role_sets[left])
            if len(left_only) != len(right_only):
                raise AssertionError("all role cell sets must have equal cardinality")
            for color in range(colors if all_colors else colors - 1):
                # After canceling common cells, equal role marginals mean
                # sum(left_only) + sum(NOT right_only) = len(right_only).
                literals = [indicator(pos, color) for pos in left_only]
                literals += [negate(indicator(pos, color)) for pos in right_only]
                gates.exactly(literals, len(right_only), cardinality)
                constraints += 1
    for pair in pairs:
        a, b = map(ROLE_NAMES.index, pair)
        if a == b:
            raise ValueError("pair marginals require two different roles")
        for ca, cb in itertools.product(range(colors), repeat=2):
            literals = [
                gates.and_gate(indicator(w[a], ca), indicator(w[b], cb))
                for w in windows
            ]
            gates.exactly(literals, colors**2, cardinality)
            constraints += 1
    stats = {
        "marginal_constraints": constraints,
        "marginal_variables": cnf.variables - before_vars,
        "marginal_clauses": len(cnf.clauses) - before_clauses,
        "variables": cnf.variables,
        "clauses": len(cnf.clauses),
        "cardinality": cardinality,
        "roles": roles,
        "pairs": list(pairs),
        "all_colors": all_colors,
        "marginal_system": marginal_system,
    }
    return cnf, cells, stats


def write_cnf(path, cnf, cells, independent_support=False, comments=()):
    with Path(path).open("w") as file:
        file.write("c Exact T-board model; all auxiliary variables are functional.\n")
        file.writelines("c " + comment + "\n" for comment in comments)
        if independent_support:
            file.write(
                "c ind "
                + " ".join(str(v) for row in cells.values() for v in row[:-1])
                + " 0\n"
            )
        file.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        file.writelines(" ".join(map(str, clause)) + " 0\n" for clause in cnf.clauses)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--colors", type=int, choices=[1, 2, 3], default=3)
    parser.add_argument("--prefix-json", type=Path)
    parser.add_argument("--prefix-name", choices=["C", "P"])
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--prefix-rows", type=int, default=6)
    parser.add_argument("--orbit-canonical", action="store_true")
    parser.add_argument("--palette-canonical", action="store_true")
    parser.add_argument(
        "--occurrence-amo",
        choices=["none", "pairwise", "binary", "tree"],
        default="tree",
    )
    parser.add_argument(
        "--cardinality", choices=["sequential", "network"], default="network"
    )
    parser.add_argument("--roles", default=ROLE_NAMES)
    parser.add_argument(
        "--marginal-system", choices=["roles", "boundary", "both"], default="roles"
    )
    parser.add_argument(
        "--pairs", default="", help="Comma-separated ordered role pairs, e.g. LM,MR,TM."
    )
    parser.add_argument("--omit-last-color", action="store_true")
    parser.add_argument("--independent-support", action="store_true")
    parser.add_argument(
        "--phase-seed",
        type=int,
        help="Rephase every variable so this known complete board is all false.",
    )
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if args.prefix_rows < 0:
        parser.error("--prefix-rows must be nonnegative")
    if args.prefix_name and not args.prefix_json:
        parser.error("--prefix-name requires --prefix-json")
    if any(r not in ROLE_NAMES for r in args.roles):
        parser.error("--roles must be a word over TLMR")
    pairs = args.pairs.split(",") if args.pairs else []
    if any(len(pair) != 2 or any(r not in ROLE_NAMES for r in pair) for pair in pairs):
        parser.error("--pairs must contain pairs of TLMR role names")
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
    cnf, cells, stats = make_marginal_cnf(
        args.colors,
        prefix,
        args.palette_canonical,
        args.occurrence_amo,
        args.orbit_canonical,
        args.cardinality,
        args.roles,
        pairs,
        not args.omit_last_color,
        args.marginal_system,
    )
    stats.update(
        {
            "colors": args.colors,
            "fixed_prefix": prefix,
            "orbit_canonical": args.orbit_canonical,
            "palette_canonical": args.palette_canonical or args.orbit_canonical,
            "independent_support": args.independent_support,
        }
    )
    if args.phase_seed is not None:
        from exact_phase import board_model, default_board, normalize_board, rephase

        mode = (
            "orbit"
            if args.orbit_canonical
            else ("palette" if args.palette_canonical else "none")
        )
        witness = normalize_board(
            default_board(args.colors, args.phase_seed), args.colors, mode
        )
        if witness[: len(prefix)] != prefix:
            parser.error("the selected phase witness does not extend the fixed prefix")
        assignment = board_model(cnf, cells, witness)
        cnf = rephase(cnf, assignment)
        stats.update(
            {
                "phase_seed": args.phase_seed,
                "phase_board": witness,
                "all_false_verified": True,
                "complemented": sum(assignment[1:]),
            }
        )
    write_cnf(args.output, cnf, cells, args.independent_support, [json.dumps(stats)])
    print(json.dumps(stats))


if __name__ == "__main__":
    main()
