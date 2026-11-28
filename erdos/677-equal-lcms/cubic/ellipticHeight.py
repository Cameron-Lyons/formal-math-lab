"""Exact checks of height and real-branch estimates for the four six-term cubics.

Run with Python 3.9+. Heights H here equal lim 4^(-k) h(x(2^k P)).
See ellipticGeometry.md for the bounds proved using these checks.
"""

from fractions import Fraction as Q
from itertools import permutations
from math import lcm

# (u, v, x(original) - x(minimal), [a2,a4,a6], mwrank generators)
MODELS = [
    (2, 1, 5, (-1, -65, 261), [(5, -6), (-7, 18), (-4, 21)]),
    (5, 2, 27, (1, -1633, 32963), [(23, -90), (-37, 210), (-31, 234)]),
    (5, 1, 13, (-1, -408, 6912), [(-24, 48), (12, -60), (-18, 90)]),
    (10, 1, 27, (1, -1633, 97763), [(-58, 27), (23, -270), (-37, 330)]),
]


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = self.lo if hi is None else Q(hi)
        assert self.lo <= self.hi

    def __add__(self, v):
        return Interval(self.lo + v.lo, self.hi + v.hi)

    def __sub__(self, v):
        return Interval(self.lo - v.hi, self.hi - v.lo)

    def __mul__(self, v):
        prod = [x * y for x in (self.lo, self.hi) for y in (v.lo, v.hi)]
        return Interval(min(prod), max(prod))

    def __truediv__(self, v):
        assert v.lo * v.hi > 0
        return self * Interval(1 / v.hi, 1 / v.lo)


def verify_infinity(u, v):
    lo, hi = Q(1), Q(3)
    for _ in range(40):
        mid = (lo + hi) / 2
        if v * mid**3 < u:
            lo = mid
        else:
            hi = mid
    assert v * lo**3 < u < v * hi**3
    t = Interval(lo, hi)
    x = Interval(4 * u * v) - Interval(2 * u * u) / (t * t) + Interval(3 * u * v) / t
    y = (
        (x * x - Interval(4 * u * u * v * v)) * t
        - Interval(3 * u * v) * x
        - Interval(6 * u**3 * v)
    ) / Interval(2 * u)
    assert x.lo > 7 and x.hi < 36 and y.hi < -9


def bezout(forms):
    """Clear denominators of representations of X^7 and Z^7 by the two quartics."""
    mat = [
        [Q(form[i - j] if 0 <= i - j < 5 else 0) for form in forms for j in range(4)]
        + [Q(i == 0), Q(i == 7)]
        for i in range(8)
    ]
    for i in range(8):
        p = next(j for j in range(i, 8) if mat[j][i])
        mat[i], mat[p] = mat[p], mat[i]
        mat[i] = [a / mat[i][i] for a in mat[i]]
        for j in range(8):
            if j != i:
                factor = mat[j][i]
                mat[j] = [a - factor * b for a, b in zip(mat[j], mat[i], strict=False)]
    den = lcm(*(row[j].denominator for row in mat for j in [8, 9]))
    sums = []
    for n, j in [(0, 8), (7, 9)]:
        coeff = [int(row[j] * den) for row in mat]
        for i in range(8):
            val = sum(
                form[i - m] * coeff[4 * k + m]
                for k, form in enumerate(forms)
                for m in range(4)
                if 0 <= i - m <= 4
            )
            assert val == (den if i == n else 0)
        sums.append(sum(abs(c) for c in coeff))
    return max(sums)


def height_interval(forms, x):
    for _ in range(6):
        p, q = x.numerator, x.denominator
        coords = [
            sum(c * p**j * q ** (4 - j) for j, c in enumerate(form)) for form in forms
        ]
        x = Q(*coords)
    bits = max(abs(x.numerator), x.denominator).bit_length()
    # 0.69314 < log 2 < 0.69315. The one-step duplication error is less than 100.
    return Interval(
        (Q(69314, 100000) * (bits - 1) - Q(100, 3)) / 4096,
        (Q(69315, 100000) * bits + Q(100, 3)) / 4096,
    )


def det(mat):
    d = len(mat)
    total = Interval(0)
    for perm in permutations(range(d)):
        sign = (-1) ** sum(
            i < j and perm[i] > perm[j] for i in range(d) for j in range(d)
        )
        term = Interval(sign)
        for i in range(d):
            term = term * mat[i][perm[i]]
        total = total + term
    return total


def positive_definite(mat):
    for d in [1, 2, 3]:
        assert det([row[:d] for row in mat[:d]]).lo > 0, (mat, d)


def check_model(u, v, shift, model, basis):
    c, d, e = model
    f = [d * d - 4 * c * e, -8 * e, -2 * d, 0, 1]
    g = [4 * e, 4 * d, 4 * c, 4, 0]
    # 2^142 < exp(100), 2^42 < exp(30).
    assert bezout([f, g]).bit_length() <= 142
    assert max(sum(map(abs, f)), sum(map(abs, g))).bit_length() <= 42
    diagonal = [height_interval([f, g], Q(x)) for x, _ in basis]
    gram = [[Interval(0)] * 3 for _ in range(3)]
    for i, (x, y) in enumerate(basis):
        assert y * y == x**3 + c * x * x + d * x + e
        gram[i][i] = diagonal[i]
        for j in range(i):
            xj, yj = basis[j]
            slope = Q(y - yj, x - xj)
            xij = slope * slope - c - x - xj
            pair = (
                height_interval([f, g], xij) - diagonal[i] - diagonal[j]
            ) / Interval(2)
            gram[i][j] = gram[j][i] = pair
    # Sylvester's criterion gives all eigenvalues in (3/20, 4).
    positive_definite(
        [
            [gram[i][j] - Interval(Q(3, 20) if i == j else 0) for j in range(3)]
            for i in range(3)
        ]
    )
    positive_definite(
        [
            [Interval(4 if i == j else 0) - gram[i][j] for j in range(3)]
            for i in range(3)
        ]
    )
    verify_infinity(u, v)
    numerator_bound = (
        9 * abs(4 * u * v - shift) + 9 * u * v + 2 * u * u + 18 * u * v + 6 * u * u
    )
    assert numerator_bound < 2048  # less than exp(8)
    print(
        f"{u}/{v}: 3/20 < Gram eigenvalues < 4; "
        "duplication error in (-100,30); 7 < x_inf < 36, y_inf < -9"
    )


if __name__ == "__main__":
    # log 2 = 2 atanh(1/3). Majorize the omitted positive terms geometrically.
    terms = 8
    z = Q(1, 3)
    partial = 2 * sum(z ** (2 * k + 1) / (2 * k + 1) for k in range(terms))
    tail = 2 * z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    assert Q(69314, 100000) < partial < partial + tail < Q(69315, 100000)
    for row in MODELS:
        check_model(*row)
