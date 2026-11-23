#!/usr/bin/env python3
"""Row-first discovery search with color-label symmetry breaking.

Python 3.10+, standard library only. Example:
  python search_n3.py --colors 3 --seconds 600
Binary control:
  python search_n3.py --colors 2 --all --seconds 30
The search may time out. TIMEOUT is never a nonexistence proof.
This discovery program is optional; verify.py checks the supplied witnesses.
"""
import argparse
import json
import sys
from time import perf_counter
from verify import geometric_check, require, as_words


def search(n, seconds, count_all=False):
    size = (n * n + 1) ** 2
    top_slots = n ** 4
    values = [0] * size
    top_counts = [0] * n
    cap = n ** 3
    endings = {r * r + j + 2: ((r - 1) ** 2 + j, r * r + j,
                              r * r + j + 1, r * r + j + 2)
               for r in range(1, n * n + 1) for j in range(2 * r - 1)}
    started = perf_counter()
    nodes = duplicate_prunes = marginal_prunes = found = 0
    first = None

    class Deadline(Exception):
        pass

    def visit(pos, seen, largest):
        nonlocal nodes, duplicate_prunes, marginal_prunes, found, first
        nodes += 1
        if nodes % 4096 == 0 and perf_counter() - started >= seconds:
            raise Deadline
        if pos == size:
            require(seen.bit_count() == n ** 4, 'invalid search leaf')
            found += 1
            if first is None:
                first = bytes(values)
            return not count_all
        win = endings.get(pos)
        base = 0
        if win:
            for i in win[:-1]:
                base = base * n + values[i]
            base *= n
        for c in range(min(n, largest + 2)):
            if pos < top_slots and top_counts[c] == cap:
                marginal_prunes += 1
                continue
            bit = 1 << (base + c) if win else 0
            if seen & bit:
                duplicate_prunes += 1
                continue
            values[pos] = c
            if pos < top_slots:
                top_counts[c] += 1
            stop = visit(pos + 1, seen | bit, max(c, largest))
            if pos < top_slots:
                top_counts[c] -= 1
            if stop:
                return True
        return False

    complete = True
    try:
        stopped_at_witness = visit(0, 0, -1)
        status = 'SAT' if found else 'UNSAT'
        complete = not stopped_at_witness
    except Deadline:
        status = 'TIMEOUT'
        complete = False
    result = dict(colors=n, status=status, canonical_solutions=found,
                  exhaustive=complete, nodes=nodes,
                  duplicate_prunes=duplicate_prunes,
                  top_color_marginal_prunes=marginal_prunes,
                  elapsed_seconds=round(perf_counter() - started, 6))
    if first is not None:
        words = as_words(first, n)
        geometric_check(n, words)
        result['first_witness_rows'] = words
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--colors', type=int, choices=[2, 3], default=3)
    parser.add_argument('--seconds', type=float, default=600)
    parser.add_argument('--all', action='store_true')
    args = parser.parse_args()
    require(args.seconds > 0, 'time limit must be positive')
    result = search(args.colors, args.seconds, args.all)
    if args.colors == 2 and args.all and result['exhaustive']:
        require(result['canonical_solutions'] == 84, 'binary canonical count mismatch')
        result['labeled_count'] = 168
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print(f'SEARCH CHECK FAILED: {type(exc).__name__}: {exc}', file=sys.stderr)
        sys.exit(1)
