"""Search rational y₁,y₂ slices of the three smooth quartic Pell orbits.

Run search_quartic_pell.py --output /tmp/quartic.jsonl, then run
uv run --with python-flint==0.9.0 quartic_rational_slices.py /tmp/quartic.jsonl

The other 24 rational coefficients can have numerator and denominator independently
as large as --coefficient-height. This search assumes the indicated 7-integral
reductions. Each twist by a 7-adic cube root of unity is tested for rationality.
"""

import argparse
import json
from fractions import Fraction
from itertools import product
from math import gcd
from multiprocessing import Pool

from flint import fmpq, fmpq_poly, fmpz_poly, nmod_mat
from quartic_first_lifts import (
    TARGET,
    P,
    QuarticLifts,
    poly_triple,
    residual,
    translate,
)

FIXED = (8, 9)  # y₁ and y₂ in the ordering x₁..x₈, y₁..y₆, z₁..z₁₂
UNKNOWN = tuple(i for i in range(26) if i not in FIXED)


def grid(height, residue):
    return [
        Fraction(a, b)
        for b in range(1, height + 1)
        if b % P
        for a in range(-height, height + 1)
        if gcd(a, b) == 1 and (a - b * residue) % P == 0
    ]


def reconstruct(value, modulus, height):
    """Bounded rational reconstruction via the extended Euclidean algorithm."""
    value %= modulus
    old_r, r, old_d, d = modulus, value, 0, 1
    while r > height:
        q, new_r = divmod(old_r, r)
        old_r, r, old_d, d = r, new_r, d, old_d - q * d
    if abs(d) > height or gcd(d, modulus) != 1 or gcd(r, d) != 1:
        return None
    assert (value * d - r) % modulus == 0
    return fmpq(r, d)


class SmoothSlice:
    def __init__(self, record, precision, height):
        self.base = tuple(fmpz_poly(record[c]) for c in "xyz")
        matrix = QuarticLifts(tuple(record[c] for c in "xyz")).matrix
        self.inverse = nmod_mat(
            [[row[j] for j in UNKNOWN] for row in matrix.tolist()], P
        ).inv()
        self.precision = precision
        self.modulus = P**precision
        self.height = height
        assert self.modulus > 2 * height**2
        # 2 mod 7 is a primitive cube root. Its Teichmüller lift yields the
        # three distinct twists of x, including both nonrational multipliers.
        w = pow(2, P ** (precision - 1), self.modulus)
        self.twists = (1, w, w * w % self.modulus)
        assert len(set(self.twists)) == 3 and pow(w, 3, self.modulus) == 1

    def lift(self, y1, y2):
        # Fix the parameters to their residues modulo the FINAL modulus from the
        # start. The minor for the remaining variables stays constant modulo 7.
        x, y, z = self.base
        y = fmpz_poly(y)
        for i, val in enumerate((y1, y2), 1):
            y[i] = val.numerator * pow(val.denominator, -1, self.modulus) % self.modulus
        triple = x, y, z
        modulus = P
        for _ in range(1, self.precision):
            error = residual(triple)
            values = [(-int(error[i]) // modulus) % P for i in range(1, 25)]
            solved = (self.inverse * nmod_mat(24, 1, values, P)).entries()
            digits = [0] * 26
            for i, v in zip(UNKNOWN, solved, strict=False):
                digits[i] = int(v)
            triple = translate(triple, modulus, poly_triple(digits))
            modulus *= P
        assert modulus == self.modulus
        assert all(int(c) % modulus == 0 for c in residual(triple))
        return triple

    def check(self, triple):
        modulus, height = self.modulus, self.height
        x, y, z = triple
        yz = []
        for f in (y, z):
            qs = []
            for a in f:
                q = reconstruct(int(a), modulus, height)
                if q is None:
                    return False, []
                qs.append(q)
            yz.append(fmpq_poly(qs))
        answers = []
        for w in self.twists:
            qs = [reconstruct(w * int(a), modulus, height) for a in x]
            if any(q is None for q in qs):
                continue
            xx = fmpq_poly(qs)
            yy, zz = yz
            identity = xx**3 + yy**2 * zz + zz**2 == fmpq_poly(TARGET)
            answers.append((identity, tuple(str(f) for f in (xx, yy, zz))))
        return True, answers


def search_orbit(args):
    record, fixed_height, precision, height = args
    model = SmoothSlice(record, precision, height)
    first, second = (grid(fixed_height, record["y"][i]) for i in (1, 2))
    all_yz = full = exact = 0
    for p, q in product(first, second):
        passed, candidates = model.check(model.lift(p, q))
        all_yz += passed
        full += len(candidates)
        for verified, triple in candidates:
            if verified:
                exact += 1
                print(f"Exact model at y₁={p} y₂={q}: {triple}", flush=True)
    return (record["x"], len(first), len(second), all_yz, full, exact)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("orbits")
    parser.add_argument("--fixed-height", type=int, default=24)
    parser.add_argument("--precision", type=int, default=64)
    parser.add_argument("--coefficient-height", type=int, default=10**26)
    parser.add_argument("--workers", type=int, default=3)
    args = parser.parse_args()
    if (
        args.fixed_height < 1
        or args.coefficient_height < args.fixed_height
        or args.precision < 1
    ):
        parser.error(
            "require positive precision and 1 ≤ fixed height ≤ coefficient height"
        )
    if P**args.precision <= 2 * args.coefficient_height**2:
        parser.error("modulus must exceed twice the square of the coefficient height")
    with open(args.orbits) as rows:
        records = [r for line in rows if (r := json.loads(line))["rank"] == 24]
    assert len(records) == 3 and all(r["orbit"] == 6 for r in records)
    jobs = [
        (r, args.fixed_height, args.precision, args.coefficient_height) for r in records
    ]
    print(
        f"Parameter height ≤ {args.fixed_height}, coefficient height ≤ {args.coefficient_height}, "
        f"precision 7^{args.precision}.",
        flush=True,
    )
    with Pool(args.workers) as workers:
        for x, n, m, yzs, full, exact in workers.imap(search_orbit, jobs):
            print(
                f"x={x}: {n}×{m}={n * m} slices; {yzs} with all Y,Z coefficients reconstructed; "
                f"{full} full triples after cube twists; {exact} exact identities.",
                flush=True,
            )


if __name__ == "__main__":
    main()
