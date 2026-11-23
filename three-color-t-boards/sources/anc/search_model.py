#!/usr/bin/env python3
"""Solver-independent CNF for the fixed-high-bit four-color construction.

Python 3.10+, standard library only. Run: python search_model.py
Optional: python search_model.py --dimacs model.cnf --witness model.sol
Existing files are never overwritten. This program builds the restricted model
and checks the provided certificate against every clause; it does not run a
SAT solver or claim unrestricted completeness of the high-bit restriction.
"""
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import argparse
import sys
from verify import load_data, flatten, geometric_check, require

B = tuple(int(c) for c in '0000100110101111')


def build_model():
    require(len({tuple(B[(k + i) % 16] for i in range(4)) for k in range(16)}) == 16,
            'B is not a binary de Bruijn cycle of order four')
    coordinates = [(r, j) for r in range(17) for j in range(2 * r + 1)]
    high = [B[(r + j) % 16] for r, j in coordinates]
    bits = list(range(1, 290))
    windows = [((r - 1) ** 2 + j, r * r + j, r * r + j + 1, r * r + j + 2)
               for r in range(1, 17) for j in range(2 * r - 1)]
    groups = defaultdict(list)
    for w in windows:
        groups[tuple(high[v] for v in w)].append(w)
    require(len(groups) == 16 and {len(g) for g in groups.values()} == {16},
            'incorrect high-bit pattern multiplicities')
    clauses = []
    auxiliary = {}

    def difference(a, b):
        if a == b:
            return None
        pair = tuple(sorted((a, b)))
        if pair not in auxiliary:
            z = 290 + len(auxiliary)
            auxiliary[pair] = z
            # z <-> (a XOR b)
            clauses.extend([[-a, -b, -z], [a, b, -z],
                            [a, -b, z], [-a, b, z]])
        return auxiliary[pair]

    compared = 0
    for group in groups.values():
        for u, v in combinations(group, 2):
            witnesses = {z for a, b in zip(u, v)
                         if (z := difference(bits[a], bits[b])) is not None}
            require(witnesses, 'two windows have no differing cell positions')
            clauses.append(sorted(witnesses))
            compared += 1
    # Two palette permutations can independently complement the low bits
    # within high-bit color 0 and high-bit color 1.
    for c in (0, 1):
        clauses.append([-bits[high.index(c)]])
    return high, bits, auxiliary, clauses, compared


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dimacs', type=Path)
    parser.add_argument('--witness', type=Path)
    args = parser.parse_args()
    high, bits, auxiliary, clauses, compared = build_model()
    words = load_data()['colorings']['4']
    geometric_check(4, words)
    flat = flatten(words)
    require([c // 2 for c in flat] == high, 'provided certificate does not fit the mask')
    values = {v: flat[i] % 2 for i, v in enumerate(bits)}
    values.update({z: values[a] ^ values[b] for (a, b), z in auxiliary.items()})
    for k, clause in enumerate(clauses):
        require(any(bool(values[abs(lit)]) == (lit > 0) for lit in clause),
                f'provided witness violates clause {k}')
    total_variables = max(values)
    print('binary cycle B=0000100110101111: all 16 cyclic length-four words PASS')
    print('high-bit groups=16; windows per group=16 PASS')
    print(f'CNF variables={total_variables}; clauses={len(clauses)}; '
          f'compared_window_pairs={compared}; shared_XORs={len(auxiliary)}')
    print('provided four-color certificate satisfies every clause PASS')
    print('scope: fixed high-bit mask; no unrestricted nonexistence claim')
    if args.dimacs:
        with args.dimacs.open('x', encoding='ascii') as f:
            f.write(f'p cnf {total_variables} {len(clauses)}\n')
            for clause in clauses:
                f.write(' '.join(map(str, clause)) + ' 0\n')
    if args.witness:
        with args.witness.open('x', encoding='ascii') as f:
            f.write('s SATISFIABLE\n')
            for i in range(1, total_variables + 1, 20):
                f.write('v ' + ' '.join(str(k if values[k] else -k)
                                       for k in range(i, min(i + 20, total_variables + 1))) + ' 0\n')


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print(f'MODEL CHECK FAILED: {type(exc).__name__}: {exc}', file=sys.stderr)
        sys.exit(1)
