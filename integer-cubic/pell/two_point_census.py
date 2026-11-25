"""Exact finite-field quartic search at two marked Pell points.

Run with: uv run --with python-flint==0.9.0 python two_point_census.py
The two source parameters are t=0 and t=1/3. Fixing the two x values leaves
seven independent coefficients. This search includes numerators divisible
by a denominator factor after reduction.
"""

import argparse
import json
from collections import Counter
from itertools import product
from multiprocessing import Pool

from flint import nmod_poly
from flint.utils.flint_exceptions import DomainError
from quartic_rational_search import admissible_pairs


def degree_twelve_choices(factors, p, mark, target_ratio):
    """Enumerate monic divisors of degree 12 having a prescribed z(mark)/z(0)."""
    terms = [
        (g.degree(), e, int(g(mark)) * pow(int(g[0]), -1, p) % p) for g, e in factors
    ]
    for exponents in product(*(range(e + 1) for _, e, _ in terms)):
        if sum(k * d for k, (d, _, _) in zip(exponents, terms, strict=False)) != 12:
            continue
        ratio = 1
        for k, (_, _, r) in zip(exponents, terms, strict=False):
            if k:
                ratio = ratio * pow(r, k, p) % p
        if ratio == target_ratio:
            yield exponents


def chunk(job):
    p, xyz, first, second = job
    x1, y1, z1 = xyz
    t = nmod_poly([0, 1], p)
    mark = pow(3, -1, p)
    ell = 1 - 3 * t**2
    unit = int(ell(mark))
    assert unit and pow(2, (p - 1) // 3, p) != 1 and (2 - x1**3) % p
    target = 2 * ell**12
    endpoint_x = x1 * pow(unit, 4, p) % p
    endpoint_y = y1 * pow(unit, 3, p) % p
    endpoint_z = z1 * pow(unit, 6, p) % p
    weights = [pow(mark, i, p) for i in range(9)]
    inv = pow(weights[8], -1, p)
    inverses = {k: pow(k, -1, p) for k in range(1, p)}
    count = Counter()
    hits = []
    for tail in product(range(p), repeat=5):
        coords = (first, second, *tail)
        last = (
            (
                endpoint_x
                - sum(c * w for c, w in zip(coords, weights[1:8], strict=False))
            )
            * inv
            % p
        )
        x = nmod_poly([0, *coords, last], p)
        f = target - x**3
        factors = f.factor()[1]
        count["x"] += 1
        for powers in degree_twelve_choices(factors, p, mark, endpoint_z):
            z = nmod_poly([1], p)
            for (g, _), k in zip(factors, powers, strict=False):
                if k:
                    z *= g**k
            z *= inverses[int(z[0])]
            square = f // z - z
            if square.degree() > 12 or square.degree() % 2:
                continue
            try:
                y = square.sqrt()
            except DomainError:
                continue
            if y[0] != 1:
                y = -y
            if int(y(mark)) != endpoint_y:
                continue
            assert int(x(mark)) == endpoint_x and int(z(mark)) == endpoint_z
            assert y[0] == 1 and z[0] == 1 and x**3 + z * (y**2 + z) == target
            hits.append(
                {k: list(map(int, f)) for k, f in zip("xyz", (x, y, z), strict=False)}
            )
    return count, hits


TARGETS = [(1, 0, -1), (-2, 3, 1)]


def census_at_five(xyz):
    # At 5 the cubic has a root. The product can lose degree and its
    # marked value can vanish, so use the full degree-bounded divisor test.
    p = 5
    mark = pow(3, -1, p)
    t = nmod_poly([0, 1], p)
    ell = 1 - 3 * t * t
    target = 2 * ell**12
    marked = [
        value * int(ell(mark)) ** d % p
        for value, d in zip(xyz, (4, 3, 6), strict=False)
    ]
    top_inverse = pow(mark**8, -1, p)
    hits = []
    for coeffs in product(range(p), repeat=7):
        x = nmod_poly([0, *coeffs], p)
        x[8] = (marked[0] - int(x(mark))) * top_inverse % p
        for y, z in admissible_pairs(target - x**3):
            if [int(y(mark)), int(z(mark))] == marked[1:]:
                hits.append(
                    {
                        k: list(map(int, f))
                        for k, f in zip("xyz", (x, y, z), strict=False)
                    }
                )
    return {"prime": p, "endpoint": xyz, "tested": p**7, "hits": hits}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, choices=[5, 7, 13], default=13)
    parser.add_argument("--workers", type=int, default=4)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--target", type=int, choices=[0, 1], default=None)
    group.add_argument("--endpoint", type=int, nargs=3, metavar=("X", "Y", "Z"))
    args = parser.parse_args()
    targets = (
        [args.endpoint]
        if args.endpoint
        else (TARGETS if args.target is None else [TARGETS[args.target]])
    )
    p = args.prime
    for x, y, z in targets:
        if x**3 + y * y * z + z * z != 2:
            parser.error("The second endpoint must satisfy the cubic.")
    if p == 5:
        for xyz in targets:
            print(json.dumps(census_at_five(xyz)), flush=True)
        return
    with Pool(args.workers) as pool:
        for xyz in targets:
            count, hits = Counter(), []
            jobs = [(p, xyz, a, b) for a, b in product(range(p), repeat=2)]
            for partial, rows in pool.imap_unordered(chunk, jobs):
                count.update(partial)
                hits.extend(rows)
            assert count["x"] == p**7
            print(
                json.dumps(
                    {
                        "prime": p,
                        "endpoint": xyz,
                        "tested": count["x"],
                        "hits": sorted(hits, key=lambda row: row["x"]),
                    }
                ),
                flush=True,
            )


if __name__ == "__main__":
    main()
