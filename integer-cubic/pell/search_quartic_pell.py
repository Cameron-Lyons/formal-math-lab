"""Enumerate mixed quartic Pell models at (0,1,1) for D=3 over F7.

Run with: uv run --with python-flint==0.9.0 search_quartic_pell.py
Use --output FILE to keep each surviving orbit as a JSON record. Coefficients
are listed in ascending order, including any leading zero coefficients.

The fractions are X/L⁴, Y/L³, Z/L⁶ with L=1−3t². Since 2 has no cube
root in F7, specializing at t=∞ shows the last numerator has degree 12.
We require gcd(X,L)=1 and use the seed X(0)=0, Y(0)=Z(0)=1. Multiplication
of X by a cube root of unity and reflection of t preserve this system.

For an exact rational lift with y of pole order ≤2, write y=E/L². The
only viable residue orbit arises by pulling back a solution with pole
bounds (2,1,3) under Pell doubling s=2t/(1+3t²). Both fixed-seed square
systems have invertible Jacobians. Hensel lifting downstairs therefore
gives a doubled 7-adic lift, and uniqueness upstairs identifies it with
the proposed rational solution. The triangular numerator substitution
has rational inverse on its image, so the lower solution would also be
rational, contrary to pole_two.md. Every orbit conjugate has the same
argument since Pell doubling commutes with reflection and with target
scaling by a 7-adic cube root of unity. This exclusion uses integral
coefficients at 7, full reduction of X, and the pole bound on y over ℚ.
"""

import argparse
import json
from collections import Counter
from itertools import product
from multiprocessing import Pool
from os import cpu_count

from flint import fmpz_poly, nmod_mat, nmod_poly
from flint.utils.flint_exceptions import DomainError

P = 7
T = nmod_poly([0, 1], P)
L = 1 - 3 * T**2
BASE = 2 * L**12
ONE = nmod_poly([1], P)


def first_nonzero(values):
    return next((x for x in values if x), 0)


def canonical_x(coeffs):
    """Normalize multiplication by a cube root of unity, then t ↦ −t."""
    for j, c in enumerate(coeffs, 1):
        if c:
            if j % 2:
                # At odd degree the sign and cube roots give every F7 unit.
                return c == 1
            # At even degree the sign still identifies the two choices of
            # sign for the first nonzero odd-degree coefficient, if present.
            return c in (1, 3) and first_nonzero(coeffs[::2]) <= 3
    return False


def degree_twelve_factors(f):
    """All divisors of f of degree twelve normalized at t=0."""
    factors = f.factor()[1]
    # Remaining degrees bound which partial products can reach twelve.
    remaining = f.degree()
    terms = [(0, ONE)]
    for g, m in factors:
        d = g.degree()
        remaining -= d * m
        powers = [g**i for i in range(min(m, 12 // d) + 1)]
        terms = [
            (k + i * d, h * gp)
            for k, h in terms
            for i, gp in enumerate(powers)
            if k + i * d <= 12 <= k + i * d + remaining
        ]
    for degree, h in terms:
        assert degree == 12
        yield h * pow(int(h[0]), -1, P)


def full_system_ranks(X, Y, Z):
    x, y, z = [fmpz_poly(list(map(int, f))) for f in (X, Y, Z)]
    t = fmpz_poly([0, 1])
    residual = x**3 + z * y**2 + z**2 - 2 * (1 - 3 * t**2) ** 12
    assert not residual[0] and all(int(c) % P == 0 for c in residual)
    columns = [
        g * t**i
        for g, degree in ((3 * x**2, 8), (2 * y * z, 6), (y**2 + 2 * z, 12))
        for i in range(1, degree + 1)
    ]
    rows = [[int(col[i]) for col in columns] for i in range(1, 25)]
    augmented = [[*row, -int(residual[i]) // P] for i, row in enumerate(rows, 1)]
    return nmod_mat(rows, P).rank(), nmod_mat(augmented, P).rank()


def coefficients(f, degree):
    return tuple(int(f[i]) for i in range(degree + 1))


def polynomial_pullback(x, y, z):
    """Test pullbacks of (3s⁴, 1+3s³, 1−2s³+2s⁶) with s=(ct+dt²)/L."""
    for c, d in product(range(P), repeat=2):
        u = c * T + d * T**2
        if (
            x == 3 * u**4
            and y == L**3 + 3 * u**3
            and z == L**6 - 2 * u**3 * L**3 + 2 * u**6
        ):
            return [c, d]
    return None


def undo_doubling(numerator, pole):
    """Undo the triangular numerator substitution for s=2t/(1+3t²)."""
    a, b = 2 * T, 1 + 3 * T**2
    remainder = numerator
    result = []
    for i in range(2 * pole + 1):
        c = int(remainder[i]) * pow(2, -i, P) % P
        result.append(c)
        remainder -= c * a**i * b ** (2 * pole - i)
    assert not remainder
    return nmod_poly(result, P)


def restricted_jacobian_det(x, e, z, d):
    """Fixed seed and pole bounds (2d,d,3d) for (x,e,z)."""
    blocks = [
        (3 * x**2, 4 * d),
        (2 * z * e * L**d, 2 * d),
        (2 * z + e**2 * L**d, 6 * d),
    ]
    columns = [p * T**i for p, n in blocks for i in range(1, n + 1)]
    return int(
        nmod_mat(
            [[int(col[i]) for col in columns] for i in range(1, 12 * d + 1)], P
        ).det()
    )


def check_classifications(records):
    """Certify the nine polynomial pullbacks and the simpler exact pole-2 case."""
    for row in records:
        x, y, z = [nmod_poly(list(row[k]), P) for k in "xyz"]
        model = polynomial_pullback(x, y, z)
        assert (model is not None) == (row["rank"] == 20)
        if model is not None:
            row["polynomial_pullback_cd"] = model
        if row["y_pole"] != 2:
            continue
        e = y // L
        assert y == e * L
        lower = [
            undo_doubling(p, k) for p, k in zip((x, e, z), (2, 1, 3), strict=False)
        ]
        a, b, c = lower
        assert a**3 + c * b**2 * L + c**2 == 2 * L**6
        assert (int(a[0]), int(b[0]), int(c[0])) == (0, 1, 1)
        assert (
            restricted_jacobian_det(*lower, 1)
            == restricted_jacobian_det(x, e, z, 2)
            == 2
        )
        row["pullback_under_pell_doubling"] = [
            coefficients(p, n) for p, n in zip(lower, (4, 2, 6), strict=False)
        ]


def search_prefix(prefix):
    searched = divisors = raw_hits = 0
    records = []
    for tail in product(range(P), repeat=8 - len(prefix)):
        c = prefix + tail
        if not canonical_x(c):
            continue
        X = nmod_poly([0, *c], P)
        if X.gcd(L).degree() > 0:
            continue
        searched += 1
        F = BASE - X**3
        for Z in degree_twelve_factors(F):
            divisors += 1
            Y2 = F // Z - Z
            if Y2.degree() % 2:
                continue
            try:
                Y = Y2.sqrt()
            except DomainError:
                continue
            if int(Y[0]) != 1:
                Y = -Y
            assert int(Y[0]) == int(Z[0]) == 1 and X**3 + Z * Y**2 + Z**2 == BASE
            x_even = not any(c[::2])
            raw_hits += 3 if x_even else 6
            y, z = coefficients(Y, 6), coefficients(Z, 12)
            reflected = tuple(
                (v if i % 2 == 0 else -v % P) for f in (y, z) for i, v in enumerate(f)
            )
            if x_even and reflected < y + z:
                continue
            orbit = 3 if x_even and reflected == y + z else 6
            reduced, y_pole = Y, 3
            while reduced % L == 0:
                reduced = reduced // L
                y_pole -= 1
            rank, augmented = full_system_ranks(X, Y, Z)
            records.append(
                {
                    "x": (0, *c),
                    "y": y,
                    "z": z,
                    "orbit": orbit,
                    "y_pole": y_pole,
                    "rank": rank,
                    "augmented": augmented,
                }
            )
    return searched, divisors, raw_hits, records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=min(4, cpu_count() or 1))
    parser.add_argument(
        "--output", help="write all surviving triples, one JSON record per line"
    )
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    total_x = total_divisors = raw = 0
    records = []
    # At the first coefficient only 0 and 1 can be canonical.
    prefixes = product((0, 1), range(P), range(P))
    with Pool(args.workers) as pool:
        for count, divisors, hits, batch in pool.imap_unordered(
            search_prefix, prefixes
        ):
            total_x += count
            total_divisors += divisors
            raw += hits
            records.extend(batch)
    records.sort(key=lambda r: (r["x"], r["y"], r["z"]))
    assert total_x == 941535 and sum(r["orbit"] for r in records) == raw
    check_classifications(records)
    print(f"{total_x} X orbits, {total_divisors} normalized degree-12 divisors")
    print(f"{len(records)} triple orbits, {raw} raw triples")
    print("y pole, Jacobian rank, augmented rank, orbits, raw triples")
    keys = [(r["y_pole"], r["rank"], r["augmented"]) for r in records]
    for key, count in sorted(Counter(keys).items()):
        print(
            *key,
            count,
            sum(r["orbit"] for k, r in zip(keys, records, strict=False) if k == key),
        )
    print(
        "Verified the nine characteristic-seven polynomial pullbacks and the one Pell doubling pullback."
    )
    if args.output:
        with open(args.output, "w") as out:
            for r in records:
                print(json.dumps(r, separators=(",", ":")), file=out)


if __name__ == "__main__":
    main()
