#!/usr/bin/env python3
"""Parsimonious CNF for T-board counting, with optional fixed prefix.

Every satisfying assignment is one labeled board. All auxiliary variables are
defined by biconditionals, so ordinary model counting requires no projection.
Use GANAK with --prob 0 for deterministic exact counting.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


class CNF:
    def __init__(self):
        self.variables = 0
        self.clauses: list[list[int]] = []

    def variable(self) -> int:
        self.variables += 1
        return self.variables

    def add(self, literals):
        self.clauses.append(list(literals))

    def conjunction(self, literals):
        """A fresh variable equivalent to the conjunction, uniquely determined."""
        literals = list(literals)
        result = self.variable()
        for literal in literals:
            self.add([-result, literal])
        self.add([result] + [-literal for literal in literals])
        return result

    def at_most_one(self, literals, method):
        """Redundant occurrence AMO constraints, with only functional auxiliaries."""
        literals = list(literals)
        if method == 'none' or len(literals) < 2:
            return
        if method == 'pairwise':
            for a, b in itertools.combinations(literals, 2):
                self.add([-a, -b])
        elif method == 'binary':
            # The caller also requires at least one literal. That chosen index
            # determines every bit, so these auxiliaries have no multiplicity.
            bits = [self.variable() for _ in range((len(literals)-1).bit_length())]
            for i, literal in enumerate(literals):
                for j, bit in enumerate(bits):
                    self.add([-literal, bit if (i >> j) & 1 else -bit])
        elif method == 'tree':
            while len(literals) > 1:
                new = []
                for i in range(0, len(literals)-1, 2):
                    a, b = literals[i:i+2]
                    self.add([-a, -b])
                    # De Morgan: -result is the disjunction a OR b.
                    result = self.conjunction([-a, -b])
                    new.append(-result)
                if len(literals) & 1:
                    new.append(literals[-1])
                literals = new
        else:
            raise ValueError(method)


def add_palette_normalization(cnf, cells, colors):
    cnf.add([cells[0][0]])
    for pos in range(len(cells)):
        for color in range(1, colors):
            cnf.add([-cells[pos][color]] +
                    [cells[earlier][color-1] for earlier in range(pos)])


def mirror_indices(colors):
    return [r*r + 2*r-j for r in range(colors*colors+1)
            for j in range(2*r+1)]


def add_reflection_normalization(cnf, cells, colors):
    """Require b <= p(reflect(b)) for each palette permutation fixing zero.

    Return comparator variables for explicit, independently checked evaluation.
    Prefix variable e[i] is equivalent to equality in all positions before i.
    Its defining clauses are biconditionals under the one-hot cell constraints.
    """
    comparisons = []
    reflected = mirror_indices(colors)
    for tail in itertools.permutations(range(1, colors)):
        permutation = (0,) + tail
        prefixes = [cnf.variable() for _ in range(len(cells)+1)]
        cnf.add([prefixes[0]])
        for pos, mirror in enumerate(reflected):
            previous, equal = prefixes[pos:pos+2]
            cnf.add([-equal, previous])
            for a in range(colors):
                for b in range(colors):
                    x, y = cells[pos][a], cells[mirror][b]
                    if a == permutation[b]:
                        cnf.add([-previous, -x, -y, equal])
                    else:
                        cnf.add([-equal, -x, -y])
                        if a > permutation[b]:
                            cnf.add([-previous, -x, -y])
        comparisons.append((permutation, prefixes))
    return comparisons


def make_cnf(colors: int, prefix: list[str], canonical: bool = False,
             occurrence_amo: str = 'tree', orbit_canonical: bool = False):
    if colors not in (1, 2, 3):
        raise ValueError('supported color counts are 1, 2, and 3')
    height = colors * colors + 1
    if len(prefix) > height or any(len(row) != 2*r+1 for r, row in enumerate(prefix)):
        raise ValueError('prefix must have row lengths 1, 3, ..., within the board')
    if any(c not in '0123456789'[:colors] for row in prefix for c in row):
        raise ValueError('prefix contains a color outside the selected palette')
    canonical = canonical or orbit_canonical
    if canonical and prefix:
        raise ValueError('palette normalization applies only to unrestricted boards')
    fixed = [int(c) for row in prefix for c in row]
    count_cells = height * height
    cnf = CNF()
    cells = {}
    for pos in range(len(fixed), count_cells):
        cells[pos] = [cnf.variable() for _ in range(colors)]
        cnf.add(cells[pos])
        for a, b in itertools.combinations(cells[pos], 2):
            cnf.add([-a, -b])
    windows = [( (r-1)**2+j, r*r+j, r*r+j+1, r*r+j+2)
               for r in range(1, height) for j in range(2*r-1)]
    used = []
    open_windows = []
    for window in windows:
        if max(window) < len(fixed):
            used.append(tuple(fixed[pos] for pos in window))
        else:
            open_windows.append(window)
    if len(set(used)) != len(used):
        cnf.add([])
        return cnf, cells
    used_set = set(used)
    patterns = [p for p in itertools.product(range(colors), repeat=4)
                if p not in used_set]
    occurrences = {p: [] for p in patterns}
    for window in open_windows:
        possible = []
        for pattern in patterns:
            if any(pos < len(fixed) and fixed[pos] != color
                   for pos, color in zip(window, pattern)):
                continue
            selector = cnf.conjunction(cells[pos][color]
                                      for pos, color in zip(window, pattern)
                                      if pos >= len(fixed))
            occurrences[pattern].append(selector)
            possible.append(selector)
        # Redundant logically, useful for propagation and excluding used patterns.
        cnf.add(possible)
    for possible in occurrences.values():
        cnf.add(possible)
        cnf.at_most_one(possible, occurrence_amo)
    if canonical:
        # Restricted-growth first occurrences: every c>0 requires an earlier c-1.
        # This selects exactly one board per palette-permutation orbit.
        add_palette_normalization(cnf, cells, colors)
    if orbit_canonical:
        add_reflection_normalization(cnf, cells, colors)
    return cnf, cells


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--colors', type=int, choices=[1, 2, 3], default=3)
    parser.add_argument('--prefix-json', type=Path)
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--prefix-name', choices=['C', 'P'],
                        help='Use a named published prefix from the certificate JSON.')
    parser.add_argument('--prefix-rows', type=int, default=6)
    parser.add_argument('--palette-canonical', action='store_true')
    parser.add_argument('--orbit-canonical', action='store_true',
                        help='Normalize colors and reflection (ternary count times 12; binary times 4).')
    parser.add_argument('--occurrence-amo', choices=['none', 'pairwise', 'binary', 'tree'], default='tree')
    parser.add_argument('--independent-support', action='store_true',
                        help='Declare cell variables as a count-preserving projection/support hint.')
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.palette_canonical = args.palette_canonical or args.orbit_canonical
    if args.prefix_rows < 0:
        parser.error('--prefix-rows must be nonnegative')
    prefix = []
    if args.prefix_name and not args.prefix_json:
        parser.error('--prefix-name requires --prefix-json')
    if args.prefix_json:
        data = json.loads(args.prefix_json.read_text())
        if isinstance(data, dict):
            if args.prefix_name:
                data = data['ternary_prefixes'][args.prefix_name]
            else:
                data = data['ternary_seeds'][args.seed]
        prefix = data if args.prefix_name else data[:args.prefix_rows]
    cnf, cells = make_cnf(args.colors, prefix, args.palette_canonical,
                         args.occurrence_amo, args.orbit_canonical)
    with args.output.open('w') as file:
        file.write('c Every model is exactly one board; auxiliary variables are functional.\n')
        file.write(f'c colors {args.colors}; fixed rows {len(prefix)}; palette canonical {args.palette_canonical}\n')
        file.write(f'c orbit canonical {args.orbit_canonical}\n')
        file.write(f'c occurrence AMO {args.occurrence_amo}; independent support hint {args.independent_support}\n')
        if args.independent_support:
            support = [v for one_hot in cells.values() for v in one_hot[:-1]]
            file.write('c ind ' + ' '.join(map(str, support)) + ' 0\n')
        file.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for clause in cnf.clauses:
            file.write(' '.join(map(str, clause)) + ' 0\n')
    print(json.dumps({'path': str(args.output), 'variables': cnf.variables,
                      'clauses': len(cnf.clauses), 'cell_variables': sum(map(len, cells.values())),
                      'fixed_prefix': prefix, 'palette_canonical': args.palette_canonical,
                      'orbit_canonical': args.orbit_canonical,
                      'occurrence_amo': args.occurrence_amo}))


if __name__ == '__main__':
    main()
