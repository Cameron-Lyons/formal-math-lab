# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.9.0"]
# ///
"""Run `uv run TernaryOtherRoots.py` for the noncube-modulo-19 pilot.
Pass `--full` for both prior coefficient blocks, deduplicated together.
"""

from argparse import ArgumentParser
from concurrent.futures import ProcessPoolExecutor
from itertools import groupby, islice
from math import gcd, isqrt
from time import perf_counter

from NormOtherRoots import other_roots, residuals
from NormSearch import K, recover
from TernaryNormSearch import CUBES_19, bit_tables, joined_root, row_candidates


A_MIN, A_MAX = 3_020_000, 3_020_999
COEFFICIENT_MAX = 12
WIDTH = 48


def seed_pairs(lo, hi, coefficient_max):
    for b in range(1, coefficient_max+1):
        for c in range(1, coefficient_max+1):
            if gcd(b, c) != 1:
                continue
            for a in row_candidates(K, b, c, lo, hi):
                result = joined_root(K, a, b, c)
                if result is None:
                    continue
                g, _, m, r = result
                assert g > 1
                if m % 3 and 54*m > 10**19 and m % 19 not in CUBES_19:
                    yield m, r


def grouped_seeds(lo, hi, coefficient_max):
    # Pack the pair into one Python integer to limit memory during the sort.
    packed = []
    for m, r in seed_pairs(lo, hi, coefficient_max):
        assert 0 <= r < m < 1 << 64
        packed.append((m << 64) | r)
    packed.sort()
    for m, group in groupby(packed, key=lambda pair: pair >> 64):
        yield m, {pair % (1 << 64) for pair in group}


def seed_classes():
    return dict(grouped_seeds(A_MIN, A_MAX, COEFFICIENT_MAX))


def make_tables():
    global tables
    tables = bit_tables(K)


def search_batch(batch):
    n_seeds = count = 0
    tested = []
    for m, joined in batch:
        seed = min(joined)
        roots = {seed, *other_roots(m, seed, K)}
        assert joined <= roots
        n_seeds += len(joined)
        count += len(roots)
        sign = 1 if m % 3 == 1 else -1
        for r in roots:
            for z in residuals(m, sign, r, 3, tables[sign], WIDTH):
                s = sign*m
                q, rem = divmod(K-z**3, s)
                assert rem == 0
                delta, rem = divmod(4*q-s*s, 3)
                assert rem == 0 and delta >= 0
                xyz = recover(s, z, K)
                tested.append((s, z, isqrt(delta), r in joined, xyz))
    return len(batch), n_seeds, count, tested


def batches(groups, size):
    while batch := list(islice(groups, size)):
        yield batch


def search(full=False):
    start = perf_counter()
    unique = n_seeds = count = 0
    tested = []
    if full:
        groups = grouped_seeds(3_000_000, 3_019_999, 40)
        with ProcessPoolExecutor(max_workers=4, initializer=make_tables) as pool:
            # Limit the number of seed sets submitted to workers at a time.
            for wave in batches(batches(groups, 3_000), 8):
                for n, s, c, rows in pool.map(search_batch, wave):
                    unique += n
                    n_seeds += s
                    count += c
                    tested.extend(rows)
    else:
        make_tables()
        unique, n_seeds, count, tested = search_batch(list(seed_classes().items()))
    hits = 0
    for s, z, gap, is_seed, xyz in tested:
        print('Survivor', s, z, gap, 'seed' if is_seed else 'additional')
        if xyz is not None:
            print('Solution', *xyz)
            hits += 1
    print('Unique moduli, joined roots, additional roots, total roots, candidate coordinates, exact square tests, solutions')
    print(unique, n_seeds, count-n_seeds, count, WIDTH*count, len(tested), hits)
    print(f'Elapsed seconds: {perf_counter()-start:.3f}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true')
    search(parser.parse_args().full)
