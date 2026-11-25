"""Search rational x in the good-reduction quartic Pell branches through (0,1,1).

    uv run --with python-flint==0.9.0 search_quartic_pell.py --output /tmp/quartic.jsonl
    uv run --with python-flint==0.9.0 quartic_rational_search.py /tmp/quartic.jsonl

The height bounds are on x alone. For each surviving X, all possible Z
dividing 2L^12-X^3 are tested over Q. See QuarticSearch.md.
"""

import argparse
import json
from collections import Counter
from functools import lru_cache
from itertools import product
from math import gcd

from flint import fmpq_poly, fmpz_poly, nmod_mat, nmod_poly
from flint.utils.flint_exceptions import DomainError


def bases():
    t = fmpz_poly([0, 1])
    L = 1 - 3 * t**2
    return {
        "numerator": [t**i for i in range(1, 9)],
        "pell": [(6 * t**2) ** i * L ** (4 - i) for i in range(1, 5)]
        + [2 * t * (6 * t**2) ** i * L ** (3 - i) for i in range(4)],
    }


def residue_vectors(records, basis):
    """Restore all cube-root twists and parameter signs before the rational search."""
    transform = nmod_mat([[int(p[i]) for p in basis] for i in range(1, 9)], 7).inv()
    numerators = set()
    for row in records:
        for zeta, sign in product((1, 2, 4), (1, -1)):
            numerators.add(tuple(zeta * row["x"][i] * sign**i % 7 for i in range(1, 9)))
    result = []
    for row in sorted(numerators):
        column = nmod_mat([[a] for a in row], 7)
        result.append(tuple(int(a) for a in (transform * column).entries()))
    return result


def admissible_pairs(F, y_seed=1):
    """Factor Z*W=F, with Z(0)=1, and solve Y²=W−Z with specified Y(0)."""
    factors = F.factor()[1]
    max_degree = 12
    remaining = F.degree()
    min_degree = max(0, remaining - max_degree)
    divisors = [F**0]
    for g, m in factors:
        remaining -= g.degree() * m
        powers = [g**i for i in range(min(m, max_degree // g.degree()) + 1)]
        divisors = [
            old * h
            for old in divisors
            for h in powers
            if min_degree - remaining <= old.degree() + h.degree() <= max_degree
        ]
    for raw in divisors:
        Z = raw / raw[0]
        square = F // Z - Z
        if square.degree() > 12 or (square and square.degree() % 2):
            continue
        try:
            Y = square.sqrt()
        except DomainError, ValueError:
            continue
        if Y[0] != y_seed:
            Y = -Y
        assert Y[0] == y_seed and Z * (Y**2 + Z) == F
        yield Y, Z


def modular_sieve(p, basis):
    t = nmod_poly([0, 1], p)
    two_L12 = 2 * (1 - 3 * t**2) ** 12
    basis_p = [nmod_poly(list(map(int, g)), p) for g in basis]

    @lru_cache(maxsize=5**8 if p == 5 else 40000)
    def passes(vector):
        X = sum(int(a) * g for a, g in zip(vector, basis_p, strict=False))
        return next(admissible_pairs(two_L12 - X**3), None) is not None

    return passes


def search_rational(records, name, basis, height):
    t = fmpq_poly([0, 1])
    L = 1 - 3 * t**2
    two_L12 = 2 * L**12
    residues = residue_vectors(records, basis)
    sieves = [(p, modular_sieve(p, basis)) for p in (3, 5, 13)]
    counts = Counter()
    hits = []
    for d in range(1, height + 1):
        if d % 7 == 0:
            continue
        reductions = [(p, pow(d, -1, p), sieve) for p, sieve in sieves if d % p]
        values = [range(-height + ((r + height) % 7), height + 1, 7) for r in range(7)]
        for residue in residues:
            choices = [values[(c * d) % 7] for c in residue]
            for coeffs in product(*choices):
                if gcd(d, *coeffs) != 1:
                    continue
                counts["tested"] += 1
                for p, inv, sieve in reductions:
                    if not sieve(tuple(c * inv % p for c in coeffs)):
                        counts[f"rejected_mod_{p}"] += 1
                        break
                else:
                    counts["exact"] += 1
                    X = (
                        fmpq_poly(
                            sum(c * g for c, g in zip(coeffs, basis, strict=False))
                        )
                        / d
                    )
                    for Y, Z in admissible_pairs(two_L12 - X**3):
                        assert two_L12 == X**3 + Z * Y**2 + Z**2
                        hits.append((X, Y, Z))
                        print(
                            f"Exact rational identity in {name} basis: X={X}, Y={Y}, Z={Z}",
                            flush=True,
                        )
    assert counts["tested"] == sum(n for k, n in counts.items() if k != "tested")
    print(
        f"{name} basis, {len(residues)} residue vectors, height {height}: "
        f"{dict(counts)}, {len(hits)} identities",
        flush=True,
    )
    return hits


def full_mod_five():
    """All X that permit a lift of the polynomial square condition over F5."""
    t = nmod_poly([0, 1], 5)
    target = 2 * (1 - 3 * t**2) ** 12
    good = set()
    for row in product(range(5), repeat=8):
        # Reflection acts on odd-index coefficients. Restore its orbit after testing.
        if next((a for a in row[::2] if a), 0) > 2:
            continue
        X = nmod_poly([0, *row], 5)
        if next(admissible_pairs(target - X**3), None) is not None:
            good.add(row)
            good.add(tuple(a * (-1) ** i % 5 for i, a in enumerate(row, 1)))
    assert len(good) == 153
    return sorted(good)


def search_coprime_denominators(records, good5, name, basis, height):
    """Combine the complete mod-5 and full-pole mod-7 X lists by CRT."""
    t = fmpq_poly([0, 1])
    target = 2 * (1 - 3 * t**2) ** 12
    mod7 = residue_vectors(records, basis)
    transform = nmod_mat([[int(g[i]) for g in basis] for i in range(1, 9)], 5).inv()
    mod5 = [
        tuple(int(a) for a in (transform * nmod_mat([[v] for v in row], 5)).entries())
        for row in good5
    ]
    residues = [
        tuple(a + 7 * ((3 * (b - a)) % 5) for a, b in zip(row7, row5, strict=False))
        for row7 in mod7
        for row5 in mod5
    ]
    sieves = [(p, modular_sieve(p, basis)) for p in (3, 11, 13)]
    counts = Counter()
    hits = []
    for d in range(1, height + 1):
        if gcd(d, 35) != 1:
            continue
        choices = [
            range(-height + ((d * r + height) % 35), height + 1, 35) for r in range(35)
        ]
        reductions = [(p, pow(d, -1, p), sieve) for p, sieve in sieves if d % p]
        for row in residues:
            for coeffs in product(*(choices[r] for r in row)):
                if gcd(d, *coeffs) != 1:
                    continue
                counts["after_CRT"] += 1
                for p, inv, sieve in reductions:
                    if not sieve(tuple(c * inv % p for c in coeffs)):
                        counts[f"rejected_mod_{p}"] += 1
                        break
                else:
                    counts["exact"] += 1
                    X = (
                        fmpq_poly(
                            sum(c * g for c, g in zip(coeffs, basis, strict=False))
                        )
                        / d
                    )
                    for Y, Z in admissible_pairs(target - X**3):
                        assert target == X**3 + Z * Y**2 + Z**2
                        hits.append((X, Y, Z))
                        print(
                            f"Exact rational identity in {name} basis: X={X}, Y={Y}, Z={Z}",
                            flush=True,
                        )
    print(
        f"{name} basis, height {height}, denominator prime to 35: "
        f"{dict(counts)}, {len(hits)} identities",
        flush=True,
    )
    return hits


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("records", help="JSONL from search_quartic_pell.py --output")
    parser.add_argument("--height", type=int, default=8)
    parser.add_argument(
        "--unit-height",
        type=int,
        default=24,
        help="extended height for denominators prime to 35 (0 to skip)",
    )
    args = parser.parse_args()
    if args.height < 1:
        parser.error("height must be positive")
    with open(args.records) as f:
        records = [json.loads(line) for line in f if line.strip()]
    if len(records) != 12:
        parser.error("expected all twelve surviving orbit representatives")
    for name, basis in bases().items():
        search_rational(records, name, basis, args.height)
    if args.unit_height > 0:
        good5 = full_mod_five()
        for name, basis in bases().items():
            search_coprime_denominators(records, good5, name, basis, args.unit_height)
