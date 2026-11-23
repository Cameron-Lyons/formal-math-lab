#!/usr/bin/env python3
"""Verify the finite certificates in 'Explicit Three- and Four-Color
Prismatic T-Tetrominoes', Qiyuan Ma.

Python 3.10+, standard library only. Run: python verify.py
Files are read relative to this script. No files are written. Explicit
exceptions keep every check active under python -O as well.
"""
from collections import Counter
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
import csv
import hashlib
import json
import re
import sys
from time import perf_counter

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_data():
    return json.loads((HERE / 'certificates.json').read_text(encoding='utf-8'))


def decode(n, words):
    require(isinstance(words, list) and len(words) == n * n + 1,
            f'n={n}: wrong number of rows')
    result = []
    for r, word in enumerate(words):
        require(isinstance(word, str) and len(word) == 2 * r + 1,
                f'n={n}: wrong length in row {r}')
        require(all(c in '0123456789'[:n] for c in word),
                f'n={n}: invalid color in row {r}')
        result.append([int(c) for c in word])
    return result


def geometric_check(n, words, orientation='T'):
    """Enumerate all translations using bottom-row anchors in the plane.

    This does not use the row-window indexing used by the counting program.
    """
    rows = decode(n, words)
    grid = {(j - r, -r): c for r, row in enumerate(rows)
            for j, c in enumerate(row)}
    if orientation == 'T':
        offsets = ((0, 1), (-1, 0), (0, 0), (1, 0))
    elif orientation == 'L':
        grid = {(x - y, y): c for (x, y), c in grid.items()}
        offsets = ((0, 1), (0, 0), (1, 0), (2, 0))
    else:
        raise ValueError('unknown orientation')
    visited = {next(iter(grid))}
    stack = list(visited)
    while stack:
        x, y = stack.pop()
        for q in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
            if q in grid and q not in visited:
                visited.add(q)
                stack.append(q)
    require(len(visited) == len(grid), 'the board is not edge-connected')
    counts = Counter()
    for x, y in grid:
        points = [(x + dx, y + dy) for dx, dy in offsets]
        if all(q in grid for q in points):
            counts[tuple(grid[q] for q in points)] += 1
    expected = set(product(range(n), repeat=4))
    missing = sorted(expected - counts.keys())
    repeated = [(p, v) for p, v in counts.items() if v != 1]
    require(not missing and not repeated,
            f'n={n} {orientation}: missing={missing[:5]}, repeated={repeated[:5]}')
    require(len(grid) == (n * n + 1) ** 2 and sum(counts.values()) == n ** 4,
            'incorrect area or number of translated windows')
    return len(grid), sum(counts.values()), len(counts)


def flatten(words):
    return bytes(int(c) for word in words for c in word)


def as_words(flat, n):
    return [''.join(str(c) for c in flat[r * r:(r + 1) ** 2])
            for r in range(n * n + 1)]


def color_reflection_orbit(words, n):
    flat = flatten(words)
    reflected = flatten([s[::-1] for s in words])
    return {bytes(p[c] for c in v) for p in permutations(range(n))
            for v in (flat, reflected)}


def check_family(seeds):
    require(len(seeds) == 5, 'the family must specify five seeds')
    family = set()
    for i, words in enumerate(seeds):
        geometric_check(3, words)
        orb = color_reflection_orbit(words, 3)
        require(len(orb) == 12, f'seed {i}: orbit is smaller than 12')
        require(not family.intersection(orb), f'seed {i}: orbits overlap')
        family.update(orb)
    require(len(family) == 60, 'the orbit union does not have size 60')
    for flat in family:
        for shape in ('T', 'L'):
            geometric_check(3, as_words(flat, 3), shape)
    return len(family)


def binary_count_by_rows():
    """Independent binary counter: row transfers with memoized states.

    Each integer encodes one complete row, least significant bit first.
    Transitions list the full set of patterns contributed between two rows.
    No color permutations or reflections are identified.
    """
    transitions_considered = 0

    @lru_cache(None)
    def transfers(r, previous):
        result = []
        for lower in range(1 << (2 * r + 1)):
            mask = 0
            for j in range(2 * r - 1):
                code = (((previous >> j) & 1) << 3
                        | ((lower >> j) & 1) << 2
                        | ((lower >> (j + 1)) & 1) << 1
                        | ((lower >> (j + 2)) & 1))
                bit = 1 << code
                if mask & bit:
                    break
                mask |= bit
            else:
                result.append((lower, mask))
        return result

    @lru_cache(None)
    def count(r, previous, used):
        nonlocal transitions_considered
        if r == 5:
            return int(used == (1 << 16) - 1)
        total = 0
        for lower, extra in transfers(r, previous):
            transitions_considered += 1
            if not used & extra:
                total += count(r + 1, lower, used | extra)
        return total

    answer = sum(count(1, apex, 0) for apex in (0, 1))
    return answer, count.cache_info().currsize, transitions_considered


def check_csv(n, words):
    rows = decode(n, words)
    with (HERE / f'n{n}_patterns.csv').open(encoding='utf-8', newline='') as f:
        records = list(csv.DictReader(f))
    require(len(records) == n ** 4, f'n={n}: incorrect CSV row count')
    codes = []
    for record in records:
        r, j = int(record['r']), int(record['j'])
        require(1 <= r <= n * n and 0 <= j <= 2 * r - 2,
                f'n={n}: CSV coordinate out of range')
        expected = (rows[r - 1][j], *rows[r][j:j + 3])
        pattern = tuple(int(record[k]) for k in ('top', 'left', 'middle', 'right'))
        require(pattern == expected, f'n={n}: incorrect CSV pattern at {(r, j)}')
        code = 0
        for c in pattern:
            code = code * n + c
        codes.append(code)
    require(codes == list(range(n ** 4)), f'n={n}: CSV patterns not complete and ordered')


def check_tex_if_available(colorings):
    source = HERE.parent / 'main.tex'
    if not source.exists():
        return False
    text = source.read_text(encoding='utf-8')
    tables = re.findall(r'\\begin\{table\}.*?\\end\{table\}', text, re.S)
    for n in (3, 4):
        matches = [t for t in tables if '\\label{tab:n' + str(n) + '}' in t]
        require(len(matches) == 1, f'n={n}: TeX certificate table missing or ambiguous')
        words = re.findall(r'^\d+ & \\texttt\{([0-9]+)\}', matches[0], re.M)
        require(words == colorings[str(n)], f'n={n}: TeX and JSON certificates disagree')
    return True


def rejection_self_tests(data):
    bad_rows = list(data['colorings']['3'])
    bad_rows[1] = bad_rows[1][:-1]
    bad_colors = ['0' * len(w) for w in data['colorings']['3']]
    tests = [('malformed row', lambda: geometric_check(3, bad_rows)),
             ('missing patterns', lambda: geometric_check(3, bad_colors)),
             ('overlapping orbits', lambda: check_family([data['ternary_seeds'][0]] * 5))]
    for name, test in tests:
        try:
            test()
        except ValueError:
            continue
        raise ValueError(f'rejection self-test failed: {name}')
    return len(tests)


def main():
    started = perf_counter()
    data = load_data()
    for n in (3, 4):
        words = data['colorings'][str(n)]
        for shape in ('T', 'L'):
            cells, windows, distinct = geometric_check(n, words, shape)
            print(f'n={n} {shape}: cells={cells} windows={windows} distinct={distinct} PASS')
        check_csv(n, words)
        print(f'n={n} inverse pattern CSV PASS')
        print(f'n={n} flat-color SHA256={hashlib.sha256(flatten(words)).hexdigest()}')
    print(f'ternary disjoint certified orbit union={check_family(data["ternary_seeds"])} PASS')
    n4 = flatten(data['colorings']['4'])
    labeled = {bytes(p[c] for c in n4) for p in permutations(range(4))}
    require(len(labeled) == 24, 'four-color label permutations are not distinct')
    for v in labeled:
        geometric_check(4, as_words(v, 4))
    print('four-color distinct global label permutations=24 PASS')
    answer, states, transfers = binary_count_by_rows()
    require(answer == 168, f'independent binary count returned {answer}, not 168')
    print(f'independent binary row-DP count={answer}; states={states}; transitions={transfers} PASS')
    print('main.tex certificate tables ' + ('MATCH PASS' if check_tex_if_available(data['colorings']) else 'not present; ancillary-only run'))
    print(f'negative-control rejection tests={rejection_self_tests(data)} PASS')
    print(f'ALL CHECKS PASS; elapsed={perf_counter() - started:.6f}s')


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print(f'VERIFICATION FAILED: {type(exc).__name__}: {exc}', file=sys.stderr)
        sys.exit(1)
