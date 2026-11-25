"""Enumerate the characteristic-seven boundary quotients through (0,1,1).

Run: uv run --with python-flint==0.9.0 python reflected_ordinate.py
"""

import json
from itertools import product
from pathlib import Path

from flint import nmod_mat, nmod_poly

P = 7
T = nmod_poly([0, 1], P)


def normalize_argument(coefficients):
    """Keep a representative under T -> cT, using the first nonzero coefficient."""
    for i, v in enumerate(coefficients, 1):
        if v:
            return v == min(v * pow(c, i, P) % P for c in range(1, P))
    return True


def factorizations(f):
    """List Q,E with f = Q E², Q(0)=1, E(0)=3, deg Q<=2, deg E<=5."""
    # deg(gcd(f,f')) >= sum floor(m/2) deg(g) for the multiplicities m.
    if 2 * f.gcd(f.derivative()).degree() + 2 < f.degree():
        return
    unit, factors = f.factor_squarefree()
    q, e = nmod_poly([int(unit)], P), nmod_poly([1], P)
    for g, m in factors:
        q *= g ** (m % 2)
        e *= g ** (m // 2)
    if q.degree() > 2:
        return
    q *= pow(int(q[0]), -1, P)
    e *= 3 * pow(int(e[0]), -1, P)
    assert q * e**2 == f
    if e.degree() <= 5:
        yield q, e
    if q.degree() == 0:
        # A quadratic Q may contain a square linear factor, including if E
        # itself has degree <=5 before removing that factor.
        for root in range(1, P):
            if e(root) == 0:
                g = 1 - T * pow(root, -1, P)
                if (e // g).degree() <= 5:
                    yield q * g * g, e // g


def census():
    ys = [(nmod_poly([1, *cs], P), cs) for cs in product(range(P), repeat=3)]
    ys = [(y, y**4 + 8, cs) for y, cs in ys]
    records = set()
    for cx in product(range(P), repeat=4):
        if not normalize_argument(cx):
            continue
        x = nmod_poly([0, *cx], P)
        for y, y4plus8, cy in ys:
            if not x and (y.degree() == 0 or not normalize_argument(cy)):
                continue
            for q, e in factorizations(y4plus8 - 4 * x**3):
                # This restriction holds after balancing, even when the two
                # coefficients of Q both lose degree on reduction.
                if not any(3 * b * b % P == int(q[2]) for b in range(P)):
                    continue
                assert q[1] != 0
                s = T * pow(int(q[1]), -1, P)
                records.add(tuple(tuple(map(int, g(s))) for g in (x, y, e, q)))
    return records


def projected_relation_ranks():
    """Ranks of the 15-monomial substitution matrix on the 12 full-pole orbits."""
    ell = 1 - 3 * T * T
    monomials = [
        (i, j, k)
        for k in range(2)
        for i in range(4)
        for j in range(5)
        if 4 * i + 3 * j + 6 * k <= 12
    ]
    assert len(monomials) == 15
    ranks = []
    rows = (
        Path(__file__).with_name("quartic_orbits_mod7.jsonl").read_text().splitlines()
    )
    for row in map(json.loads, rows):
        x, y, z = [nmod_poly(row[key], P) for key in "xyz"]
        w = 2 * z + y * y
        columns = [
            x**i * y**j * w**k * ell ** (12 - 4 * i - 3 * j - 6 * k)
            for i, j, k in monomials
        ]
        matrix = nmod_mat([[int(f[a]) for f in columns] for a in range(25)], P)
        ranks.append(matrix.rank())
    return sorted(ranks)


if __name__ == "__main__":
    unit = [((0, 0, a), (1, 2), (3, 1, 2), (1, 1, 6)) for a in (1, 2, 4)]
    linear = [
        (x, (1, 1, 5), (3, 5, 1, 1, 2), (1, 1))
        for x in ((0, 3, 6, 5), (0, 6, 5, 3), (0, 5, 3, 6))
    ]
    assert census() == set(unit + linear)
    print("All normalized nonconstant reductions are the six listed cases.")
    ranks = projected_relation_ranks()
    assert ranks == [10] * 10 + [14] * 2
    print("The 15-monomial relation has nullity five on ten orbits and one on two.")
