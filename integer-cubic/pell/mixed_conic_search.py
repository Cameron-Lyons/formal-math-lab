"""Test all eight coefficients of quartic abscissas on several Pell conics.

For each fixed x, one polynomial factorization over Q enumerates all possible
y and z in the specified chart. Congruence tests discard incompatible x first.
"""

import argparse
from collections import Counter
from functools import cache, lru_cache
from itertools import product
from math import gcd, isqrt

from even_abscissa_search import chart
from flint import fmpq_poly, nmod_poly
from quartic_rational_search import admissible_pairs


def chart_data(t, D, x0):
    L, even = chart(t, D)
    odd = [2 * t * (2 * D * t**2) ** j * L ** (3 - j) for j in range(4)]
    return x0 * L**4, even + odd, 2 * L**12


def scan(seed, discriminants, height, max_d):
    x0, y0, z0 = seed
    assert z0 == 1 and x0**3 + y0**2 + 1 == 2
    primes = [p for p in (3, 5, 7, 11, 13, 17, 19) if (2 - x0**3) % p]

    @cache
    def data(p, D):
        return chart_data(nmod_poly([0, 1], p), D, x0)

    @lru_cache(maxsize=400000)
    def passes(p, D, row):
        constant, basis, target = data(p, D)
        X = constant + sum(a * f for a, f in zip(row, basis, strict=False))
        return next(admissible_pairs(target - X**3, y0 % p), None) is not None

    counts = Counter()
    values = range(-height, height + 1)
    for d in range(1, max_d + 1):
        tests = [(p, pow(d, -1, p)) for p in primes if d % p]
        for row in product(values, repeat=8):
            if not any(row[4:]) or (row[3] == 0 and row[7] == 0) or gcd(d, *row) != 1:
                continue
            counts["abscissas"] += 1
            surviving = discriminants
            for p, inv in tests:
                reduced = tuple(a * inv % p for a in row)
                surviving = [D for D in surviving if passes(p, D % p, reduced)]
                if not surviving:
                    break
            for D in surviving:
                counts["exact_tests"] += 1
                constant, basis, target = chart_data(fmpq_poly([0, 1]), D, x0)
                X = constant + sum(a * f for a, f in zip(row, basis, strict=False)) / d
                for Y, Z in admissible_pairs(target - X**3, y0):
                    assert target == X**3 + Y**2 * Z + Z**2
                    counts["identities"] += 1
                    print("EXACT", seed, D, X, Y, Z, flush=True)
        print(seed, "denominator through", d, dict(counts), flush=True)
    return counts


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=int, default=1)
    parser.add_argument("--max-d", type=int, default=6)
    parser.add_argument("--max-D", type=int, default=80)
    args = parser.parse_args()
    Ds = [
        D
        for D in range(2, args.max_D + 1)
        if all(D % (k * k) for k in range(2, isqrt(D) + 1))
    ]
    print("squarefree D", Ds, flush=True)
    for seed in ((0, 1, 1), (1, 0, 1), (-2, 3, 1)):
        print("total", seed, dict(scan(seed, Ds, args.height, args.max_d)), flush=True)
