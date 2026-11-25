"""Complete the degree-six ordinary reduction check for cubic Pell substitutions.

Run with python-flint 0.9.0. The independent quintic check fixes the smaller
cubic factor of 2-x³. The sextic check fixes x and enumerates all eligible z.
"""

from itertools import product

from flint import nmod_poly
from flint.utils.flint_exceptions import DomainError

P = 13
T = nmod_poly([0, 1], P)
SQUARES = {a * a % P for a in range(P)}
UNITS = range(1, P)
INVERSES = {a: pow(a, -1, P) for a in UNITS}


def check_candidate(x, z, quotient):
    square = quotient - z
    if square and (
        square.degree() % 2 or int(square.leading_coefficient()) not in SQUARES
    ):
        return
    if int(square[0]) not in SQUARES:
        return
    try:
        y = square.sqrt()
    except DomainError:
        return
    assert x**3 + z * (z + y**2) == 2
    raise AssertionError(f"nonconstant solution {(x, y, z)}")


def quintic_by_cubic_factor():
    cubics = set()
    for a, b in product(range(P), repeat=2):
        if all((i**3 + a * i + b) % P for i in range(P)):
            cubics.add(min((a * k**2 % P, b * k**3 % P) for k in UNITS))

    assert len(cubics) == 6
    tested = 0
    for a, b in sorted(cubics):
        f = T**3 + a * T + b
        roots = []
        for cs in product(range(P), repeat=3):
            r = nmod_poly(list(cs), P)
            if (r**3 - 2) % f == 0:
                roots.append(r)
        # Multiplication of x by a constant cube root of unity relates the
        # three roots in the quotient field and permutes the polynomials h.
        assert len(roots) == 3
        assert all(any(v == r * roots[0] for r in (1, 3, 9)) for v in roots)
        for cs in product(range(P), repeat=3):
            x = roots[0] + f * nmod_poly(list(cs), P)
            quotient, remainder = divmod(2 - x**3, f)
            assert not remainder
            for j in UNITS:
                check_candidate(x, j * f, INVERSES[j] * quotient)
                tested += 1
    assert tested == 158184
    print(f"Six cubic factor orbits, {tested} scalar tests, no solutions.")


def sextic_by_x():
    # Translation kills the quintic coefficient. Scaling t and multiplying
    # x by a cube root of unity give the following leading coefficients.
    leaders = {min(a * k**6 * r % P for k in UNITS for r in (1, 3, 9)) for a in UNITS}
    assert leaders == {1, 2}
    one = nmod_poly([1], P)
    x_count = divisor_count = 0
    for a in sorted(leaders):
        for cs in product(range(P), repeat=5):
            x = nmod_poly([*cs, 0, a], P)
            f = 2 - x**3
            divisors = [one]
            for g, multiplicity in f.factor()[1]:
                degree = g.degree()
                if degree <= 6:
                    divisors = [
                        v * g**i
                        for v in divisors
                        for i in range(
                            min(multiplicity, (6 - v.degree()) // degree) + 1
                        )
                    ]
            x_count += 1
            for z in divisors:
                if z.degree() == 6:
                    divisor_count += 1
                    quotient = f // z
                    for j in UNITS:
                        if (-(a**3) * INVERSES[j]) % P in SQUARES:
                            check_candidate(x, j * z, INVERSES[j] * quotient)
    assert (x_count, divisor_count) == (742586, 737856)
    print(f"{x_count} sextic x, {divisor_count} monic sextic divisors, no solutions.")


if __name__ == "__main__":
    quintic_by_cubic_factor()
    sextic_by_x()
