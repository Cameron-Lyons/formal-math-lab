"""Two exhaustive checks for polynomial solutions of z²+y²z+x³=2 over F13.

The two quartic checks allow deg x≤4, deg y≤3 and arbitrary z.
A further check exhausts the quintic degree pattern. Run with
uv run --with python-flint==0.9.0 ordinary_polynomial_search.py.
The characteristic-zero consequence and normalization are in OrdinaryPolynomial.md.
"""

from collections import Counter
from itertools import product

from flint import nmod_poly
from flint.utils.flint_exceptions import DomainError

P = 13
T = nmod_poly([0, 1], P)
ONE = nmod_poly([1], P)
SQUARES = {i * i % P for i in range(P)}


def normalized_x():
    roots_of_unity = [c for c in range(1, P) if c**3 % P == 1]
    for degree in range(1, 5):
        # Translation kills the degree-(d−1) coefficient. Scaling the
        # parameter and multiplying x by a cube root of 1 normalize its lead.
        leads = {
            min(a * s**degree * c % P for s in range(1, P) for c in roots_of_unity)
            for a in range(1, P)
        }
        for a in sorted(leads):
            for lower in product(range(P), repeat=degree - 1):
                yield a * T**degree + nmod_poly(list(lower), P)


def factor_search(xs):
    divisors = tested = hits = 0
    for x in xs:
        f = 2 - x**3
        _, factors = f.factor()
        # Each tuple of exponents gives a distinct monic divisor.
        parts = [ONE]
        for g, exponent in factors:
            powers = [g**i for i in range(min(6 // g.degree(), exponent) + 1)]
            parts = [
                h * q for h in parts for q in powers if h.degree() + q.degree() <= 6
            ]
        for h in parts:
            if f.degree() - h.degree() > 6:
                continue
            quotient, remainder = divmod(f, h)
            assert not remainder
            divisors += 1
            for a in range(1, P):
                z = a * h
                y_squared = pow(a, -1, P) * quotient - z
                tested += 1
                if y_squared and y_squared.degree() % 2:
                    continue
                try:
                    y = y_squared.sqrt()
                except DomainError:
                    continue
                assert y.degree() <= 3 and z**2 + z * y**2 + x**3 == 2
                hits += 1
    return divisors, tested, hits


def evaluation_search(xs):
    """Try all y directly using point evaluations followed by a squarefree test."""
    ys = [nmod_poly(list(row), P) for row in product(range(P), repeat=4)]
    fourth_powers = [y**4 + 8 for y in ys]
    masks = []
    for t in range(P):
        # Collect y by y(t)^4, converting the bits to one integer per bucket.
        buckets = [bytearray((len(ys) + 7) // 8) for _ in range(P)]
        for j, y in enumerate(ys):
            value = pow(int(y(t)), 4, P)
            buckets[value][j // 8] |= 1 << (j % 8)
        by_value = [int.from_bytes(b, "little") for b in buckets]
        masks.append(
            [
                sum(
                    bits
                    for v, bits in enumerate(by_value)
                    if (v + 8 - 4 * a**3) % P in SQUARES
                )
                for a in range(P)
            ]
        )
    passed = hits = 0
    for x in xs:
        viable = (1 << len(ys)) - 1
        for t in range(P):
            viable &= masks[t][int(x(t))]
        cube = 4 * x**3
        while viable:
            bit = viable & -viable
            viable -= bit
            y_index = bit.bit_length() - 1
            discriminant = fourth_powers[y_index] - cube
            passed += 1
            if not discriminant:
                hits += 1
            elif discriminant.degree() % 2 == 0:
                lead, factors = discriminant.factor_squarefree()
                if int(lead) in SQUARES and all(not (e % 2) for _, e in factors):
                    hits += 1
    return len(xs) * len(ys), passed, hits


def quintic_search():
    # F13 units have order 12, so fifth powers give all leading coefficients.
    # Translation kills the quartic coefficient. One of z and −z−y² has
    # degree three. It divides 2−x³ and is irreducible up to its scalar.
    count = divisors = hits = 0
    for lower in product(range(P), repeat=4):
        count += 1
        x = T**5 + nmod_poly(list(lower), P)
        f = 2 - x**3
        for factor, _ in f.factor()[1]:
            if factor.degree() != 3:
                continue
            quotient, remainder = divmod(f, factor)
            assert not remainder
            divisors += 1
            for a in range(1, P):
                z = a * factor
                y_squared = pow(a, -1, P) * quotient - z
                try:
                    y = y_squared.sqrt()
                except DomainError:
                    continue
                assert y.degree() == 6 and x**3 + z * y**2 + z**2 == 2
                hits += 1
    return count, divisors, hits


def main():
    assert all(a**3 % P != 2 for a in range(P))
    xs = list(normalized_x())
    counts = Counter(x.degree() for x in xs)
    assert counts == {1: 1, 2: 26, 3: 169, 4: 8788}
    print("Normalized x counts:", dict(sorted(counts.items())), flush=True)
    divisors, tested, hits = factor_search(xs)
    print(
        f"Factor search: {divisors} monic divisors, {tested} scalar multiples, {hits} hits",
        flush=True,
    )
    count, passed, square_hits = evaluation_search(xs)
    print(
        f"Direct search: {count} pairs, {passed} pass point evaluation, {square_hits} hits"
    )
    assert square_hits == hits == 0
    count, divisors, hits = quintic_search()
    assert count == P**4 and hits == 0
    print(
        f"Quintic search: {count} normalized x, {divisors} cubic divisors, "
        f"{12 * divisors} scalar multiples, {hits} hits"
    )
    x, y, z = [
        nmod_poly(row, P)
        for row in (
            [5, 5, 2, 5, 2, 0, 1],
            [1, 4, 5, 0, 10],
            [8, 4, 3, 7, 1, 2, 7, 5, 2, 5],
        )
    ]
    assert x.degree() == 6 and x**3 + y**2 * z + z**2 == 2
    print("Verified a nonconstant degree-six example over F13.")


if __name__ == "__main__":
    main()
