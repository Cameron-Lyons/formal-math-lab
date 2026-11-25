"""Cubic Pell substitutions through (0,1,1), both choices of the cubic z factor.

Runs over F13 for D=2 and 3, then tests constant reduction over F169.
Requires python-flint 0.9.0. All polynomial coefficient lists are ascending.
"""

from collections import Counter
from itertools import product

from flint import fmpz_poly, fq_default_poly, fq_default_poly_ctx, nmod_mat, nmod_poly
from flint.utils.flint_exceptions import DomainError
from search_pell_mod import possible_z

P = 13
SEEDS_Z = (1, -2)
T = nmod_poly([0, 1], P)


def x_orbits():
    """Choose the lexicographically least coefficients under x↦ζx and t↦±t."""

    def extend(coeffs, group):
        if len(coeffs) == 7:
            yield nmod_poly(coeffs, P)
            return
        i = len(coeffs)
        for c in range(P):
            images = [(c * r * e**i % P, (r, e)) for r, e in group]
            if min(v for v, _ in images) == c:
                yield from extend([*coeffs, c], [g for v, g in images if v == c])

    yield from extend([0], list(product((1, 3, 9), (1, -1))))


def order(poly, factor):
    assert poly
    n = 0
    while poly % factor == 0:
        poly //= factor
        n += 1
    return n


def verify_full_residue(triple):
    x, y, z = (fmpz_poly(list(map(int, r))) for r in triple)
    z[0] = -2
    assert list(x) == [0, 2, 6, 2, 12, 2, 3]
    assert list(y) == [1, 11, 0, 10, 11, 3, 5]
    assert list(z) == [-2, 7, 6, 3, 5, 6, 6]
    t = fmpz_poly([0, 1])
    l = 1 - 3 * t**2
    error = x**3 + z * y**2 + z**2 * l**3 - 2 * l**9
    assert error[0] == 0 and all(c % P == 0 for c in error)
    columns = [
        d * t**j
        for d in (3 * x**2, 2 * y * z, y**2 + 2 * z * l**3)
        for j in range(1, 7)
    ]
    j = nmod_mat([[int(c[i]) for c in columns] for i in range(1, 19)], P)
    rhs = nmod_mat([[-int(error[i]) // P] for i in range(1, 19)], P)
    w = nmod_mat([[11, 10, 8, 3, 4, 0, 1, 3, 0, 4, 10, 7, 1, 12, 3, 11, 9, 1]], P)
    assert j.rank() == 17 and not any((w * j).entries()) and int((w * rhs)[0, 0]) == 4


def check_conic(d):
    l = 1 - d * T**2
    l3, const = l**3, 2 * l**9
    poles = [g for g, _ in l.factor()[1]]
    counts = {z0: Counter() for z0 in SEEDS_Z}
    n = 0
    for x in x_orbits():
        n += 1
        f = const - x**3
        for z1 in possible_z(f.factor()[1], P, 1):
            quotient = f // z1
            for z0 in SEEDS_Z:
                z = z0 * z1
                square = quotient * pow(z0, -1, P) - z * l3
                if square.degree() > 12 or square.degree() % 2:
                    continue
                try:
                    y = square.sqrt()
                except DomainError:
                    continue
                if y[0] != 1:
                    y = -y
                assert y[0] == 1 and z * (y**2 + z * l3) == f
                if x == 0 and y == l3 and z == z0 * l3:
                    counts[z0]["constant"] += 1
                elif any(
                    order(x, g) == 1 and order(y, g) >= 2 and z % g for g in poles
                ):
                    counts[z0]["pole obstruction"] += 1
                else:
                    assert (d, z0) == (3, -2)
                    verify_full_residue((x, y, z))
                    counts[z0]["no first correction"] += 1
    assert n == 804835
    assert counts[1] == {"constant": 1, "pole obstruction": 1 if d == 2 else 2}
    if d == 2:
        assert counts[-2] == counts[1]
    else:
        assert counts[-2] == {
            "constant": 1,
            "pole obstruction": 2,
            "no first correction": 1,
        }
    print(f"D={d}, {n} numerator representatives, {counts}", flush=True)


def check_quadratic_residue_field():
    polynomials = fq_default_poly_ctx(13, 2, "a")
    k = polynomials.base_field()
    elements = [k(i) + k(j) * k.gen() for i, j in product(range(P), repeat=2)]
    units = [c for c in elements if c != k.zero()]

    def key(c):
        return tuple(c.to_list())

    for j, expected in ((1, 28561), (2, 338), (3, 1)):
        # Normalize the first nonzero coefficient x_j by scaling t and x.
        scales = {key(s**j * k(c)): s**j * k(c) for s in units for c in (1, 3, 9)}
        leaders = [
            v for v in units if key(v) == min(key(v * r) for r in scales.values())
        ]
        tested = 0
        for c in leaders:
            for cs in product(elements, repeat=3 - j):
                x = fq_default_poly([k.zero()] * j + [c, *cs], polynomials)
                f = polynomials(2) - x**3
                divisors = [polynomials.one()]
                for g, m in f.factor()[1]:
                    divisors = [
                        z * g**i
                        for z in divisors
                        for i in range(min(m, (3 - z.degree()) // g.degree()) + 1)
                    ]
                for divisor in divisors:
                    for z0 in SEEDS_Z:
                        z = z0 * divisor / divisor[0]
                        square = f // z - z
                        if square.degree() > 6 or square.degree() % 2:
                            continue
                        try:
                            y = square.sqrt()
                        except DomainError:
                            continue
                        assert x**3 + z * (y**2 + z) == polynomials(2)
                        raise AssertionError(
                            f"ordinary solution over F169: {(x, y, z)}"
                        )
                tested += 1
        assert tested == expected
        print(
            f"F169, first nonzero x coefficient at {j}, {tested} representatives, zero hits."
        )


if __name__ == "__main__":
    for discriminant in (2, 3):
        check_conic(discriminant)
    check_quadratic_residue_field()
