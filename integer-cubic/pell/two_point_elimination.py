"""Eliminate W from both ends of the quartic chart over the rationals.

Run with uv run --with python-flint==0.9.0 python two_point_elimination.py.
Optional --msolve FILE exports the primitive integer equations.
"""

import argparse
from functools import reduce
from math import gcd, lcm
from pathlib import Path

from flint import fmpq_mpoly_ctx, fmpz_poly


TARGETS = ((1, 0, -1), (-2, 3, 1))


def mul(a, b):
    product = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            product[i+j] += x*y
    return product


def equations(target, low=6, high=5):
    """Use coefficients 1..low and 23..24-high to recover W linearly."""
    assert 0 <= low and 0 <= high and low + high <= 11
    free_w = list(range(low + 1, 12 - high))
    names = ([f'a{i}' for i in range(1, 8)] + [f'b{i}' for i in range(1, 6)]
             + [f'w{i}' for i in free_w])
    ring = fmpq_mpoly_ctx.get(tuple(names))
    gen = ring.gens()
    x1, y1, z1 = target
    x = [0, *gen[:7], 6**4*x1]
    y = [1, *gen[7:12], 6**3*y1]
    w = [ring.constant(0) for _ in range(13)]
    w[0], w[12] = ring.constant(3), ring.constant(6**6*(2*z1+y1*y1))
    assert w[12]
    for j, variable in zip(free_w, gen[12:]):
        w[j] = variable
    ell_term = 8*fmpz_poly([1, 6, 6])**12
    y2 = mul(y, y)
    rhs = [ring.constant(int(ell_term[i])) + s - 4*c
           for i, (s, c) in enumerate(zip(mul(y2, y2), mul(mul(x, x), x)))]

    def recover(coeffs, source, count):
        for j in range(1, count + 1):
            known = sum(coeffs[k]*coeffs[j-k] for k in range(1, j))
            coeffs[j] = (source[j]-known)/(2*coeffs[0])
        return coeffs

    w = recover(w, rhs, low)
    w = recover(w[::-1], rhs[::-1], high)[::-1]
    residuals = [a-b for a, b in zip(mul(w, w), rhs)]
    assert all(not residuals[i] for i in [*range(low+1), *range(24-high, 25)])
    middle = residuals[low+1:24-high]
    assert len(middle) == len(names)
    return names, middle


def primitive(f):
    coeffs = f.coeffs()
    den = lcm(*(int(c.denominator) for c in coeffs))
    content = reduce(gcd, (int(c*den) for c in coeffs))
    return f*den/content


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--target', type=int, choices=(0, 1), default=0)
    parser.add_argument('--low', type=int, default=6)
    parser.add_argument('--high', type=int, default=5)
    parser.add_argument('--msolve', type=Path)
    parser.add_argument('--characteristic', type=int, default=0)
    args = parser.parse_args()
    names, polys = equations(TARGETS[args.target], args.low, args.high)
    print(f'{len(names)} variables, {len(polys)} equations')
    print('degrees:', [int(f.total_degree()) for f in polys])
    print('term counts:', [len(f) for f in polys])
    if args.msolve:
        body = ',\n'.join(str(primitive(f)).replace(' ', '') for f in polys)
        args.msolve.write_text(','.join(names) + f'\n{args.characteristic}\n' + body + '\n')


if __name__ == '__main__':
    main()
