"""Search x=(a*y²+b*y+c)/d for a square times a polynomial of degree ≤2.

Run with: uv run --with python-flint==0.9.0 search_quadratics.py [height]
"""
import argparse
from itertools import product
from math import gcd

from flint import fmpz_poly, nmod_poly


def odd_part_degree(polynomial):
    """Degree left after removing the largest polynomial square divisor."""
    _, factors = polynomial.factor_squarefree()
    return sum(factor.degree() for factor, exponent in factors if exponent % 2)


def residue_table(p):
    """For each leading and linear coefficient, keep admissible constants mod p."""
    y = nmod_poly([0, 1], p)
    base = y**4 + 8
    table = {}
    for a, b in product(range(p), repeat=2):
        quadratic = (a * y + b) * y
        table[a, b] = [
            c for c in range(p)
            if odd_part_degree(base - 4 * (quadratic + c)**3) <= 2
        ]
    return table


def search(height):
    # A square times a quadratic still has that form after good reduction.
    # Gauss's lemma lets us reduce primitive integer factors at p, even when
    # the leading coefficient drops. We skip primes dividing the denominator.
    primes = [7, 11, 13, 17, 19]
    tables = {p: residue_table(p) for p in primes}
    y = fmpz_poly([0, 1])
    for d in range(1, height + 1):
        # Bit i represents the integer c = i-height. Converting the residue
        # tables to masks lets each test discard many constants at once.
        filters = []
        for p in primes:
            if d % p == 0:
                continue
            inv = pow(d, -1, p)
            masks = [sum(1 << (c + height)
                         for c in range(-height + (r + height) % p, height + 1, p))
                     for r in range(p)]
            table = {(a, b): sum(masks[c * d % p] for c in cs)
                     for (a, b), cs in tables[p].items()}
            filters.append((p, inv, table))
        for a in range(-height, height + 1):
            # Changing y to -y accounts for the other sign of b.
            for b in range(int(a == 0), height + 1):
                candidates = (1 << (2 * height + 1)) - 1
                for p, inv, table in filters:
                    candidates &= table[a * inv % p, b * inv % p]
                    if not candidates:
                        break
                while candidates:
                    bit = candidates & -candidates
                    candidates ^= bit
                    c = bit.bit_length() - 1 - height
                    if gcd(a, b, c, d) != 1:
                        continue
                    delta = d**3 * (y**4 + 8) - 4 * ((a*y+b)*y+c)**3
                    if odd_part_degree(delta) <= 2:
                        yield a, b, c, d


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("height", type=int, default=256, nargs="?")
    args = parser.parse_args()
    if args.height < 1:
        parser.error("height must be positive")
    for coefficients in search(args.height):
        print(*coefficients)
