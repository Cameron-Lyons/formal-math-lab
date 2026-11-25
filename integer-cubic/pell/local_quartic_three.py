"""One-mark ordinary quartics and quadratic graphs at the prime 3.

Run with uv run --with python-flint==0.9.0 python local_quartic_three.py.
"""

from fractions import Fraction
from itertools import product

from flint import fmpz_mpoly_ctx, fmpz_poly, nmod_mat, nmod_poly

DIMS = (4, 3, 6)
T = fmpz_poly([0, 1])


def ordinary_reductions():
    triples = []
    for y_digits in product(range(3), repeat=3):
        y = nmod_poly([1, *y_digits], 3)
        for z_digits in product(range(3), repeat=6):
            z = nmod_poly([1, *z_digits], 3)
            cube = 2 - z * (z + y * y)
            if cube.derivative():
                continue
            x = nmod_poly([cube[3 * i] for i in range(5)], 3)
            assert x**3 == cube and not x[0]
            if x.degree() > 0:
                triples.append(tuple(fmpz_poly(list(map(int, f))) for f in (x, y, z)))
    return triples


def integer_poly(f, half):
    # Embed E_i=t^i/3^floor(i/2) by substituting t=3s for the half-slope algebra.
    return fmpz_poly([c * 3 ** ((i + 1) // 2) for i, c in enumerate(f)]) if half else f


def coefficients(f, half):
    digits = []
    for i in range(1, 13):
        factor = 3 ** ((i + 1) // 2) if half else 1
        q, r = divmod(int(f[i]), factor)
        assert r == 0
        digits.append(q)
    return digits


def residual(triple, half=False):
    x, y, z = (integer_poly(g, half) for g in triple)
    err = x**3 + z * (z + y * y) - 2
    assert err[0] == 0 and err.degree() <= 12
    return coefficients(err, half)


def jacobian(triple, half=False):
    x, y, z = (integer_poly(g, half) for g in triple)
    cols = [
        coefficients(deriv * integer_poly(T**i, half), half)
        for deriv, d in zip((3 * x * x, 2 * y * z, y * y + 2 * z), DIMS, strict=False)
        for i in range(1, d + 1)
    ]
    return nmod_mat(list(map(list, zip(*cols, strict=False))), 3)


def as_triple(digits):
    return tuple(fmpz_poly([0, *digits[l:r]]) for l, r in ((0, 4), (4, 7), (7, 13)))


def add_correction(a, v, modulus):
    return tuple(f + modulus * g for f, g in zip(a, v, strict=False))


def levels(base):
    """All extendible lifts in one fixed integer-slope residue class."""
    J = jacobian(base)
    rank = J.rank()
    I = nmod_mat(
        [r + [int(i == j) for j in range(12)] for i, r in enumerate(J.tolist())], 3
    )
    rows = [list(map(int, r)) for r in I.rref()[0].tolist()]
    pivots = [next(i for i in range(13) if row[i]) for row in rows[:rank]]
    sol = [tuple((i, a) for i, a in enumerate(row[13:]) if a) for row in rows]
    ker, n = J.nullspace()
    basis = [[int(ker[i, j]) for i in range(13)] for j in range(n)]
    # Delay kernel enumeration for an inconsistent branch.
    corrections = None
    nodes = [base]
    stats = []
    for modulus in (3, 9, 27, 81):
        nxt = []
        for node in nodes:
            err = residual(node)
            assert all(e % modulus == 0 for e in err)
            rhs = [(-e // modulus) % 3 for e in err]
            if any(sum(rhs[i] * v for i, v in row) % 3 for row in sol[rank:]):
                continue
            assert modulus < 81
            particular = [0] * 13
            for idx, row in zip(pivots, sol, strict=False):
                particular[idx] = sum(rhs[i] * v for i, v in row) % 3
            if corrections is None:
                corrections = [
                    as_triple(
                        [
                            sum(k[i] * a for k, a in zip(basis, u, strict=False)) % 3
                            for i in range(13)
                        ]
                    )
                    for u in product(range(3), repeat=n)
                ]
            center = add_correction(node, as_triple(particular), modulus)
            nxt.extend(add_correction(center, k, modulus) for k in corrections)
        stats.append(len(nxt))
        nodes = nxt
        if not nodes:
            break
    return tuple(stats)


def ordinary():
    reductions = ordinary_reductions()
    choices = [
        [
            t
            for t in reductions
            if all(all(i % e == 0 or not a for i, a in enumerate(f)) for f in t)
        ]
        for e in range(1, 7)
    ]
    assert list(map(len, choices)) == [26, 2, 0, 0, 0, 0]
    results = [levels(t) for t in reductions]
    assert results.count((0,)) == 24 and results.count((81, 6561, 177147, 0)) == 2
    ok_half = 0
    free = [(j, i) for j, d in enumerate(DIMS) for i in range(1, d + 1, 2)]
    for base in choices[1]:
        for bits in product(range(3), repeat=len(free)):
            triple = [fmpz_poly(f) for f in base]
            for (j, i), v in zip(free, bits, strict=False):
                triple[j][i] = v
            r = residual(triple, True)
            if any(e % 3 for e in r):
                continue
            ok_half += 1
            J = jacobian(triple, True)
            aug = nmod_mat(
                [[*row, -v // 3] for row, v in zip(J.tolist(), r, strict=False)], 3
            )
            assert (J.rank(), aug.rank()) == (9, 10)
    assert ok_half == 18
    print(
        "Ordinary maps: 24 integer-slope classes stop mod 9; both others stop mod 243."
    )
    print(
        "The 18 half-slope classes stop mod 9; larger slope denominators give no classes."
    )


def valuation(a):
    v = 0
    assert a
    while a % 3 == 0:
        v += 1
        a //= 3
    return v


def root_bound(p):
    data = [(i, valuation(int(a))) for i, a in enumerate(p) if a]
    intersections = {Fraction(v - w, j - i) for i, v in data for j, w in data if i != j}
    slopes = set()
    for s in intersections:
        v = min(a + i * s for i, a in data)
        if s.denominator == 1 and sum(a + i * s == v for i, a in data) >= 2:
            slopes.add(int(s))
    assert slopes == {0}
    for prec in (3, 9, 27, 81):
        if all(int(p(i)) % prec for i in range(prec) if i % 3):
            return prec
    raise AssertionError("A unit root mod 81 survived")


def quadratic_graphs():
    ctx = fmpz_mpoly_ctx.get(("s", "A", "B"))
    s, a, b = ctx.gens()
    f = (1 + s) ** 4 + 8 - 4 * (a * s * s + b * s) ** 3
    disc = f.discriminant("s")
    content, factors = disc.factor()
    invariant = next(v for v, m in factors if v.degrees()[2])
    assert disc == content * a**3 * invariant
    assert [(k, int(c)) for k, c in invariant.to_dict().items() if k[2] == 14] == [
        ((0, 1, 14), 59049)
    ]
    projection = invariant.discriminant("B")
    assert projection.degrees()[0] == 0 and projection.degrees()[2] == 0
    q = fmpz_poly(
        [
            projection.to_dict().get((0, i, 0), 0)
            for i in range(projection.degrees()[1] + 1)
        ]
    )
    checks = [
        (g.degree(), m, root_bound(g)) for g, m in q.factor()[1] if g.degree() > 1
    ]
    assert sorted(checks) == [(6, 2, 9), (24, 3, 3), (48, 2, 81)]
    assert [g for g, m in q.factor()[1] if g.degree() == 1] == [T]
    print(
        "Quadratic graphs: projected factor degrees, multiplicities, obstructing unit moduli",
        checks,
    )


if __name__ == "__main__":
    ordinary()
    quadratic_graphs()
