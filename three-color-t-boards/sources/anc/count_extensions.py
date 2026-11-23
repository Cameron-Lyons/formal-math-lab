#!/usr/bin/env python3
"""Exact cell-by-cell enumeration for the paper's two prescribed prefixes.
Python 3.10+, standard library only. Run: python count_extensions.py
This counts all binary colorings, and only the stated ternary prefix fibers.
It does not count all ternary colorings. No files are written.
"""
from time import perf_counter
import sys
from verify import load_data, decode, geometric_check, require, as_words


def count_extensions(n, prefix):
    require(len(prefix) <= n * n + 1, 'too many prefix rows')
    require(all(len(row) == 2 * r + 1 for r, row in enumerate(prefix)),
            'malformed prefix')
    require(all(isinstance(c, int) and 0 <= c < n for row in prefix for c in row),
            'invalid prefix color')
    size = (n * n + 1) ** 2
    values = [c for row in prefix for c in row]
    first_free = len(values)
    values.extend([0] * (size - first_free))
    windows = {r * r + j + 2: ((r - 1) ** 2 + j, r * r + j,
                              r * r + j + 1, r * r + j + 2)
               for r in range(1, n * n + 1) for j in range(2 * r - 1)}
    used = 0
    for end, window in windows.items():
        if end < first_free:
            code = 0
            for i in window:
                code = code * n + values[i]
            require(not (used >> code & 1), 'prefix contains a repeated window')
            used |= 1 << code
    nodes = duplicate_prunes = 0
    solutions = []

    def visit(pos, seen):
        nonlocal nodes, duplicate_prunes
        nodes += 1
        if pos == size:
            require(seen.bit_count() == n ** 4, 'incomplete pattern set at leaf')
            solutions.append(bytes(values))
            return
        window = windows.get(pos)
        base = 0
        if window:
            for i in window[:-1]:
                base = base * n + values[i]
            base *= n
        for color in range(n):
            bit = 1 << (base + color) if window else 0
            if seen & bit:
                duplicate_prunes += 1
                continue
            values[pos] = color
            visit(pos + 1, seen | bit)

    visit(first_free, used)
    return solutions, nodes, duplicate_prunes


def main():
    started = perf_counter()
    data = load_data()
    solutions, nodes, prunes = count_extensions(2, [])
    require(len(set(solutions)) == len(solutions) == 168, 'binary count mismatch')
    for v in solutions:
        geometric_check(2, as_words(v, 2))
    print(f'binary complete count=168; nodes={nodes}; duplicate_prunes={prunes} PASS', flush=True)
    seeds = {bytes(int(c) for w in s for c in w) for s in data['ternary_seeds']}
    for name, prefix in data['ternary_prefixes'].items():
        t = perf_counter()
        solutions, nodes, prunes = count_extensions(3, [[int(c) for c in w] for w in prefix])
        require(len(solutions) == len(set(solutions)) == 2, f'prefix {name}: expected two extensions')
        require(set(solutions) <= seeds, f'prefix {name}: extensions absent from certificate seeds')
        for v in solutions:
            geometric_check(3, as_words(v, 3))
        print(f'ternary prefix {name}: completions=2 COMPLETE; nodes={nodes}; '
              f'duplicate_prunes={prunes}; elapsed={perf_counter() - t:.6f}s PASS', flush=True)
    print('ternary unrestricted total: NOT COMPUTED')
    print(f'ALL COUNTS PASS; elapsed={perf_counter() - started:.6f}s')


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print(f'COUNT FAILED: {type(exc).__name__}: {exc}', file=sys.stderr)
        sys.exit(1)
