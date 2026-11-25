"""Enumerate reflected quartic charts fixing x,z through (0,1,1).

Run with uv run --with python-flint==0.9.0 python reflected_factor.py.
Coefficients in output start at the constant term.
"""

from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, isqrt

from flint import fmpq, fmpq_poly, fmpz_poly, nmod_mat, nmod_poly
from flint.utils.flint_exceptions import DomainError
from quartic_rational_slices import reconstruct
from quartic_reflection import factors


def shapes(h):
    """All h=Q E² with Q(0)=E(0)=1, deg Q<=2, deg E<=2."""
    p = int(h.modulus())
    assert h[0] == 1
    q, e = nmod_poly([1], p), nmod_poly([1], p)
    for g, m in h.factor_squarefree()[1]:
        unit_g = g * pow(int(g[0]), -1, p)
        q *= unit_g ** (m % 2)
        e *= unit_g ** (m // 2)
    if q.degree() <= 2 and e.degree() <= 2:
        yield q, e
    if q.degree() == 0:
        t = nmod_poly([0, 1], p)
        for root, _ in e.roots():
            g = 1 - t * pow(int(root), -1, p)
            e1 = e // g
            if e1.degree() <= 2:
                yield g * g, e1


def census(p, pell_three=True):
    """Representatives up to scaling the variable. Skip fully constant X,Z."""
    t = nmod_poly([0, 1], p)
    records = set()
    minimal = {
        i: {min(a * pow(c, i, p) % p for c in range(1, p)) for a in range(1, p)}
        for i in range(1, 5)
    }
    choices = (
        (0,) * (i - 1) + (a,) + tail
        for i in range(1, 5)
        for a in sorted(minimal[i])
        for tail in product(range(p), repeat=4 - i)
    )
    for coeffs in choices:
        x = nmod_poly([0, *coeffs], p)
        for z, h in factors(x):
            for q, e in shapes(h):
                if pell_three and not any(3 * b * b % p == q[2] for b in range(p)):
                    continue
                assert x**3 + z * z + q * e * e * z == 2
                scales = [pow(int(q[1]), -1, p)] if q[1] else range(1, p)
                records.add(
                    min(
                        tuple(tuple(map(int, poly(t * c))) for poly in (x, e, z, q))
                        for c in scales
                    )
                )
    return records


def jacobian(record, p):
    x, e, z, q = (nmod_poly(list(cs), p) for cs in record)
    t = nmod_poly([0, 1], p)
    cols = [
        deriv * t**i
        for deriv, deg in ((3 * x * x, 4), (2 * z * q * e, 2), (2 * z + q * e * e, 6))
        for i in range(1, deg + 1)
    ]
    return nmod_mat([[int(pol[i]) for pol in cols] for i in range(1, 13)], p)


def independent_seven():
    """Independent check via the discriminant, without factoring 2-X³."""
    p = 7
    cubics = [
        (nmod_poly([0, *cs], p), cs) for cs in product(range(p), repeat=4) if any(cs)
    ]
    shifts = [(8 - 4 * x**3, cs) for x, cs in cubics]
    records = set()
    for a, k, e1, e2 in product((0, 1), range(p), range(p), range(p)):
        e = nmod_poly([1, e1, e2], p)
        q = nmod_poly([1, a, k], p)
        y2 = q * e * e
        y4 = y2 * y2
        for shift, cs in shifts:
            try:
                w = (y4 + shift).sqrt()
            except DomainError:
                continue
            if int(w[0]) != 3:
                w = -w
            assert w[0] == 3
            z = (w - y2) * 4
            assert z[0] == 1 and a == 1
            x = nmod_poly([0, *cs], p)
            records.add(tuple(tuple(map(int, g)) for g in (x, e, z, q)))
    assert records == census(p, False) and len(records) == 9


def local_filter(rows, p, pell_three):
    # All prime-field records are obtained after rescaling the variable to
    # retain a nonconstant coefficient of X. This prime is used only when
    # every resulting quadratic has nonzero linear coefficient. Then every
    # original normalized rational solution has p-integral coefficients.
    assert rows and all(len(r[3]) >= 2 and r[3][1] == 1 for r in rows)
    allowed = {r[3][2] if len(r[3]) == 3 else 0 for r in rows}

    def quad(a, b):
        v = a * pow(b, -1, p) % p
        return (3 * v * v if pell_three else v) % p

    return {(a, b) for b in range(1, p) for a in range(p) if quad(a, b) in allowed}


def lift(record, inverse, p, k, height):
    limit = p
    while limit <= 2 * height**2:
        limit *= p
    quadratic = k.numerator * pow(k.denominator, -1, limit) % limit
    q = fmpz_poly([1, 1, quadratic])
    polys = [fmpz_poly(list(row)) for row in record[:3]]
    modulus = p
    while modulus < limit:
        x, e, z = polys
        error = x**3 + z * z + q * e * e * z - 2
        digits = [(-int(error[i]) // modulus) % p for i in range(1, 13)]
        delta = iter((inverse * nmod_mat(12, 1, digits, p)).entries())
        for i, degree in enumerate((4, 2, 6)):
            polys[i] += modulus * fmpz_poly(
                [0] + [int(next(delta)) for _ in range(degree)]
            )
        modulus *= p
    x, e, z = polys
    assert all(int(c) % limit == 0 for c in x**3 + z * z + q * e * e * z - 2)
    rationals = []
    for poly in polys:
        cs = [reconstruct(int(c), limit, height) for c in poly]
        if None in cs:
            return None
        rationals.append(fmpq_poly(cs))
    x, e, z = rationals
    q = fmpq_poly([1, 1, fmpq(k.numerator, k.denominator)])
    return rationals if x**3 + z * z + q * e * e * z == fmpq_poly([2]) else None


def search(b_height, height, pell_three):
    primes = [7, 13, 19, 37, 67, 79]
    params = [
        Fraction(a, b)
        for b in range(1, b_height + 1)
        for a in range(1, b_height + 1)
        if gcd(a, b) == 1
    ]
    p = 0
    rows = []
    for p in primes:
        rows = sorted(census(p, pell_three))
        allowed = local_filter(rows, p, pell_three)
        params = [b for b in params if (b.numerator % p, b.denominator % p) in allowed]
        print(f"After {p}: {len(params)} positive parameters", flush=True)
    assert p == 79 and len(rows) == (33 if pell_three else 66)
    pell_params = [
        b
        for b in params
        if pell_three
        or isqrt(b.numerator * b.denominator) ** 2 != b.numerator * b.denominator
    ]
    if pell_params:
        first = min(pell_params, key=lambda b: (max(b.numerator, b.denominator), b))
        print(
            f"Least-height survivor with positive nonsquare leading term: {first}",
            flush=True,
        )
    by_quadratic = {}
    for row in rows:
        assert len(row[3]) == 3
        by_quadratic.setdefault(row[3][2], []).append((row, jacobian(row, p).inv()))
    count = 0
    sol = 0
    for b in params:
        k = 3 * b * b if pell_three else b
        quad = k.numerator * pow(k.denominator, -1, p) % p
        for r, inverse in by_quadratic[quad]:
            count += 1
            answer = lift(r, inverse, p, k, height)
            if answer:
                sol += 1
                print("Exact identity", b, answer, flush=True)
    print(f"{count} smooth branches, {sol} exact identities", flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("primes", type=int, nargs="*")
    parser.add_argument("--parameter-height", type=int)
    parser.add_argument("--coefficient-height", type=int, default=10**60)
    parser.add_argument(
        "--general", action="store_true", help="use k directly instead of k=3B²"
    )
    parser.add_argument("--check-seven", action="store_true")
    args = parser.parse_args()
    for prime in args.primes or (
        [] if args.parameter_height or args.check_seven else [7, 13]
    ):
        rows = census(prime, not args.general)
        counts = Counter((r[3], jacobian(r, prime).rank()) for r in rows)
        print(prime, len(rows), sorted(counts.items()), flush=True)
    if args.parameter_height:
        search(args.parameter_height, args.coefficient_height, not args.general)
    if args.check_seven:
        independent_seven()
        print("Independent discriminant census at 7 matches all nine records.")
