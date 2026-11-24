"""Endpoint and scaling checks for quartic Pell substitutions fixed by reflection.

Run with: uv run --with python-flint==0.9.0 quartic_reflection.py
The variable in the enumerations is t=u-1. Polynomial lists are ascending.
"""

from fractions import Fraction
from functools import reduce
from math import gcd
from itertools import product

from flint import nmod_mat, nmod_poly
from flint.utils.flint_exceptions import DomainError


def square_times(polynomial, shape):
    """Return the monic square root and the actual scalar, or None."""
    quotient, remainder = divmod(polynomial, shape)
    if remainder or not quotient or quotient.degree() > 4:
        return None
    p = int(polynomial.modulus())
    scalar = int(quotient.leading_coefficient())
    try:
        root = (quotient * pow(scalar, -1, p)).sqrt()
    except DomainError:
        return None
    assert polynomial == scalar * shape * root**2
    return root, scalar


def factors(c, bound=6):
    """The two factors have degrees at most six, and each equals 1 at zero."""
    p = int(c.modulus())
    f = 2-c**3
    divisors = [nmod_poly([1], p)]
    for g, m in f.factor()[1]:
        divisors = [z*g**i for z in divisors
                    for i in range(min(m, (bound-z.degree())//g.degree()) + 1)]
    for z in divisors:
        if f.degree()-z.degree() <= 6:
            j = z * pow(int(z[0]), -1, p)
            yield j, f//j-j


def census(p):
    t = nmod_poly([0, 1], p)
    shapes = {'positive': t, 'negative': t**2, 'unit': t*(t+2)}
    records = {kind: [] for kind in shapes}
    constant = 0
    for coefficients in product(range(p), repeat=4):
        c = nmod_poly([1, *coefficients], p)
        for j, h in factors(c):
            if not h:
                assert c == 1 and j == 1
                constant += 1
                continue
            for kind, shape in shapes.items():
                pair = square_times(h, shape)
                if pair:
                    e, k = pair
                    records[kind].append((c, j, e, k))
    assert constant == 1
    return records


def second_endpoint(record):
    c, j, _, _ = record
    return int(c(-2)), int(j(-2))


def multiples(p):
    """The reductions of n*(-1,1) in the coordinates (C,J)=(-X,Y)."""
    base = (-1 % p, 1)
    x, y = base
    orbit = [None]
    while True:
        orbit.append(((-x) % p, y))
        u, v = base
        if x == u and (y+v) % p == 0:
            return orbit
        slope = (3*x*x*pow(2*y, -1, p) if x == u
                 else (y-v)*pow(x-u, -1, p)) % p
        xx = (slope*slope-x-u) % p
        x, y = xx, (slope*(x-xx)-y) % p
        assert (y*y-x**3-2) % p == 0


def check_endpoint_13(records):
    p = 13
    t = nmod_poly([0, 1], p)
    same = [r for r in records if second_endpoint(r) == (1, 1)]
    opposite = [r for r in records if second_endpoint(r) == (1, 12)]
    assert len(same) == len(opposite) == 2
    for c, j, e, k in same:
        assert c(-t-2) == c and j(-t-2) == j and e(-t-2) == -e
        shape = t*(t+2)
        columns = ([3*c**2*t**i for i in range(1, 5)] +
                   [(2*j+k*shape*e**2)*t**i for i in range(1, 7)] +
                   [2*k*shape*e*j*t**i for i in range(3)])
        rows = [[int(col[i]) for col in columns] for i in range(1, 13)]
        rows += [[(-2)**i for i in range(1, 5)]+[0]*9,
                 [0]*4+[(-2)**i for i in range(1, 7)]+[0]*3]
        assert nmod_mat(rows, p).rank() == 13
    assert all((c.degree(), j.degree(), e.degree()) == (2, 3, 0)
               for c, j, e, _ in opposite)


def bad_positive_scale(p):
    """Test for a positive-scale residue where neither maximal degree survives."""
    t = nmod_poly([0, 1], p)
    # The shape t and its arbitrary scalar remain valid under scaling t by a unit.
    for d in range(1, 4):
        leading = {min(a*k**d % p for k in range(1, p)) for a in range(1, p)}
        for a in leading:
            for cs in product(range(p), repeat=d-1):
                c = nmod_poly([1, *cs, a], p)
                for _, h in factors(c, bound=5):
                    if square_times(h, t):
                        return True
    return False


def endpoint_exists(p, point):
    """Exhaust the unit-scale system with both endpoint values prescribed."""
    if point == (1, 1):
        return True
    x2, z2 = point
    t = nmod_poly([0, 1], p)
    shape = t*(t+2)
    for cs in product(range(p), repeat=3):
        a = (x2-1-sum(x*(-2)**i for i, x in enumerate(cs, 1))) * pow(16, -1, p) % p
        c = nmod_poly([1, *cs, a], p)
        for j, h in factors(c):
            if int(j(-2)) == z2 and square_times(h, shape):
                return True
    return False


def denominator_valuation(x, p):
    d, v = x.denominator, 0
    while d % p == 0:
        v += 1
        d //= p
    return v


def rational_multiples(bound):
    """Exact abscissas for the finite sieve; x(-nP) = x(nP)."""
    x, y = Fraction(-1), Fraction(1)
    out = [None]
    for n in range(1, bound + 1):
        out.append(x)
        m = 3*x*x/(2*y) if n == 1 else (y-1)/(x+1)
        xx = m*m-x+1
        x, y = xx, m*(x-xx)-y
        assert y*y == x**3+2
    return out


def main():
    counts = {11: (0, 140, 46), 13: (12, 0, 30), 19: (72, 72, 16)}
    allowed = {}
    for p in (11, 13, 19):
        records = census(p)
        assert tuple(len(records[key]) for key in ('positive', 'negative', 'unit')) == counts[p]
        assert all(c.degree() == 4 or j.degree() == 6 for c, j, _, _ in records['positive'])
        for c, j, e, k in records['positive']:
            t = nmod_poly([0, 1], p)
            support = [i for f in (c, j, k*t*e**2)
                       for i in range(1, f.degree()+1) if f[i]]
            assert c.degree() == 4 and reduce(gcd, support) == 1
        if p == 13:
            check_endpoint_13(records['unit'])
        points = {second_endpoint(r) for r in records['unit']} | {(1, 1)}
        if records['positive']:
            points.add(None)
        orbit = multiples(p)
        allowed[p] = (len(orbit), {n for n, pt in enumerate(orbit) if pt in points})
        print(f"p={p}: scale counts {counts[p]}, endpoint indices {allowed[p]}", flush=True)
    assert allowed == {
        11: (12, {1, 3, 5, 7, 9, 11}),
        13: (19, {0, 1, 4, 6, 7, 8, 9, 10, 11, 12, 18}),
        19: (13, {0, 1, 12}),
    }
    exact_x = rational_multiples(100)
    assert denominator_valuation(exact_x[19], 13) == 2
    assert denominator_valuation(exact_x[13], 19) == 2
    candidates = {n for n in range(-100, 101)
                  if abs(n) > 1 and all(n % order in ns for order, ns in allowed.values())
                  and all(denominator_valuation(exact_x[abs(n)], p) % 4 == 0 for p in (13, 19))}
    assert candidates == {-77, -53, -51, -27, 25, 27, 77}
    tests = {47: (-77, -51, 77), 59: (-27, 25), 61: (-53,), 97: (27,)}
    for p, indices in tests.items():
        assert not bad_positive_scale(p)
        orbit = multiples(p)
        endpoints = {orbit[n % len(orbit)] for n in indices}
        assert None not in endpoints and (1, 1) not in endpoints
        assert all(not endpoint_exists(p, point) for point in endpoints)
        candidates.difference_update(indices)
        print(f"p={p}: excluded endpoint indices {indices}", flush=True)
    assert not candidates


if __name__ == "__main__":
    main()
