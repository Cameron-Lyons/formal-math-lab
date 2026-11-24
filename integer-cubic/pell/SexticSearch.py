"""Enumerate the boundary residues of degree-six ordinary substitutions.

The default run verifies the mod-5 obstruction. --seeds-at-13 also
enumerates the degree-(6,4,9) residues and the possible marked triples.
Run with uv run --with python-flint==0.9.0 SexticSearch.py.
"""

import argparse
from collections import Counter
from itertools import product

from flint import fmpz_poly, nmod_mat, nmod_poly
from flint.utils.flint_exceptions import DomainError


def monic_divisors(f, bound):
    one = nmod_poly([1], f.modulus())
    divisors = [one]
    for g, m in f.factor()[1]:
        divisors = [v*g**i for v in divisors
                    for i in range(min(m, (bound-v.degree())//g.degree())+1)]
    return divisors


def square_root(f, bound):
    if f.degree() > 2*bound or (f and f.degree() % 2):
        return None
    try:
        return f.sqrt()
    except DomainError:
        return None


def five():
    p = 5
    t = nmod_poly([0, 1], p)
    seen = set()
    profiles = set()
    count = Counter()
    for cs in product(range(p), repeat=7):
        if not any(cs[1:]):
            continue
        x = nmod_poly(list(cs), p)
        if tuple(map(int, x)) in seen:
            continue
        # These changes fix the leading coefficient of a degree-four x over F5.
        for s, h in product(range(1, p), range(p)):
            seen.add(tuple(map(int, x(s*t+h))))
        count['abscissas'] += 1
        f = 2-x**3
        for d in monic_divisors(f, 9):
            for j in range(1, p):
                z = j*d
                y = square_root(f//z-z, 4)
                if y is None:
                    continue
                assert x**3 + z*(z+y**2) == 2
                assert (x.degree(), y.degree(), z.degree()) == (4, 3, 6)
                profiles.add(int(x[4]))
                count['divisor and scalar hits'] += 1
    assert len(seen) == p**7-p
    assert count == {'abscissas': 4075, 'divisor and scalar hits': 12}
    assert profiles == {2, 4}
    print('F5: 4075 x orbits, 12 hits, all of degrees (4,3,6) and x_4 in {2,4}.')

    checked = 0
    for a, b, u, v, w in product(sorted(profiles), range(1, p), *[range(p)]*3):
        if any((u, v, w)):
            a_poly, b_poly = a*t**2 + v*t + u, b*t + w
            assert square_root(t**2*b_poly**4-4*a_poly**3, 3) is None
            checked += 1
    assert checked == 992
    print('F5: 992 second-scale profiles with a nonzero lower term, zero squares.')


def thirteen():
    p = 13
    seeds = set()
    marked = set()
    count = Counter()
    # As in cubic_ordinary_at13.py, translation kills x_5 and scaling by
    # t↦ct and x↦ζx leaves leading coefficient 1 or 2. The degree-nine
    # factors have the same leading coefficient, whose square is −x_6³.
    for a in (1, 2):
        scalars = [j for j in range(1, p) if (j*j+a**3) % p == 0]
        if not scalars:
            continue
        for cs in product(range(p), repeat=5):
            x = nmod_poly([*cs, 0, a], p)
            count['x'] += 1
            f = 2-x**3
            for divisor in monic_divisors(f, 9):
                if divisor.degree() != 9:
                    continue
                for j in scalars:
                    z = j*divisor
                    y = square_root(f//z-z, 4)
                    if y is None:
                        continue
                    assert x**3 + z*(z+y**2) == 2
                    assert y.degree() == 4
                    count['hits'] += 1
                    for s in range(p):
                        for c, sign in product((1, 3, 9), (1, -1)):
                            seed = (int(c*x(s)), int(sign*y(s)), int(z(s)))
                            seeds.add(seed)
                            if seed == (11, 3, 1):
                                t = nmod_poly([0, 1], p)
                                assert int(x.derivative()(s)) != 0
                                scale = pow(int(c*x.derivative()(s)), -1, p)
                                parameter = scale*t + s
                                marked.add(tuple(tuple(map(int, r)) for r in
                                                 (c*x(parameter), sign*y(parameter), z(parameter))))
    assert count == {'x': p**5, 'hits': 24}
    assert len(seeds) == 116
    assert (1, 0, 1) not in seeds and (11, 3, 1) in seeds
    print('F13: 24 full-degree hits, realizing 116 seed residues.')
    assert len(marked) == 1
    return marked.pop()


def check_height(r, modulus, bound):
    # Reduce a basis for a ≡ rb mod modulus. Only the certificate below
    # uses its output, so the bound does not rely on optimal reduction.
    v, w = (modulus, 0), (r, 1)
    while True:
        if sum(x*x for x in w) < sum(x*x for x in v):
            v, w = w, v
        norm = sum(x*x for x in v)
        dot = sum(x*y for x, y in zip(v, w))
        step = (2*dot+norm)//(2*norm)
        if step == 0:
            break
        w = (w[0]-step*v[0], w[1]-step*v[1])
    assert abs(v[0]*w[1]-v[1]*w[0]) == modulus
    for a, b in (v, w):
        assert (a-r*b) % modulus == 0
        assert (abs(a)+abs(b))*bound < modulus


def exceptional_seed(row):
    p = 13
    x, y, z = (fmpz_poly(list(r)) for r in row)
    x[0], y[0], z[0] = -2, 3, 1
    assert x[1] == 1
    coordinates = (x, y, z)
    coefficients = [(k, i) for k, d in enumerate((6, 4, 9))
                    for i in range(1, d+1) if (k, i) != (0, 1)]
    t = fmpz_poly([0, 1])
    derivatives = (3*x**2, 2*y*z, y**2+2*z)
    columns = [derivatives[k]*t**i for k, i in coefficients]
    jacobian = nmod_mat([[int(c[i]) for c in columns] for i in range(1, 19)], p)
    inverse = jacobian.inv()
    modulus = p
    for _ in range(699):
        error = x**3+z*y**2+z**2-2
        assert all(c % modulus == 0 for c in error)
        target = nmod_mat([[-int(error[i])//modulus] for i in range(1, 19)], p)
        for (k, i), digit in zip(coefficients, (inverse*target).entries()):
            coordinates[k][i] += modulus*int(digit)
        modulus *= p
    assert all(c % modulus == 0 for c in (x**3+z*y**2+z**2-2))
    for k, i in coefficients:
        check_height(int(coordinates[k][i]), modulus, 10**388)
    print('(-2,3,1), x′(0)=1: unique lift modulo 13^700, all 18 free coefficients exceed height 10^388.')


if __name__ == '__main__':
    args = argparse.ArgumentParser()
    args.add_argument('--seeds-at-13', action='store_true')
    args.add_argument('--exceptional-seed', action='store_true')
    options = args.parse_args()
    five()
    if options.seeds_at_13 or options.exceptional_seed:
        marked = thirteen()
        if options.exceptional_seed:
            exceptional_seed(marked)
