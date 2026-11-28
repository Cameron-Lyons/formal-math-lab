"""Find the exact nearest nonzero reciprocal-subset gap by modular filtering.

Run with Python 3.10+, for example: python3 exact_gaps.py 71 100
Each output row gives N, the signed attained sum minus 1, and its denominators.
"""

from __future__ import annotations

import argparse
from bisect import bisect_left, bisect_right
from collections import defaultdict
from fractions import Fraction
from heapq import heapify, heappop, heappush
from math import gcd, lcm


def subset_totals(denominators, scale):
    """Index each sum by the bit mask selecting its denominators."""
    totals = [0]
    for n in denominators:
        weight = scale // n
        totals += [x + weight for x in totals]
    return totals


def selected(denominators, mask):
    return [d for i, d in enumerate(denominators) if mask & (1 << i)]


def prime_powers(n):
    """Factor n into maximal powers of its distinct primes."""
    p = 2
    while p * p <= n:
        power = 1
        while n % p == 0:
            n //= p
            power *= p
        if power > 1:
            yield p, power
        p += 1
    if n != 1:
        yield n, n


class SmoothSums:
    """Represent subsets of the divisors of D that lie in [2,N]."""

    def __init__(self, n, divisor, base):
        self.divisor = divisor
        self.base = base
        assert divisor % base == 0
        smooth = [d for d in range(2, n + 1) if divisor % d == 0]
        self.base_denominators = [d for d in smooth if base % d == 0]
        # prefixes[j] marks exactly the base numerators attainable after j steps.
        self.prefixes = [1]
        for d in self.base_denominators:
            prev = self.prefixes[-1]
            self.prefixes.append(prev | (prev << (base // d)))
        bits = self.prefixes[-1]
        self.table = bits.to_bytes((bits.bit_length() + 7) // 8, "little")

        # Each block corresponds to extra powers of a prime in D/base.
        # A denominator qualifying for several primes would couple their
        # residues. Keep it in the outer enumeration instead (see solve).
        extra = [d for d in smooth if base % d != 0]
        self.blocks = []
        factors = list(prime_powers(divisor // base))
        groups = defaultdict(list)
        for d in extra:
            missing = d // gcd(base, d)
            primes = [p for p, _ in factors if missing % p == 0]
            if len(primes) == 1:
                groups[primes[0]].append(d)
        for p, modulus in factors:
            ds = groups[p]
            options = defaultdict(dict)
            for mask, total in enumerate(subset_totals(ds, divisor)):
                options[total % modulus][total] = mask
            self.blocks.append((modulus, ds, options))
        self.denominators = set(self.base_denominators)
        for _, ds, _ in self.blocks:
            self.denominators.update(ds)

    def represent(self, target):
        if target < 0:
            return None
        choices = []
        for modulus, ds, options in self.blocks:
            available = options.get(target % modulus)
            if not available:
                return None
            choices.append((ds, available))
        choices.sort(key=lambda part: len(part[1]))

        def visit(j, remainder):
            if remainder < 0:
                return None
            if j < len(choices):
                ds, options = choices[j]
                for total, mask in options.items():
                    rest = visit(j + 1, remainder - total)
                    if rest is not None:
                        return rest + selected(ds, mask)
                return None
            u, residue = divmod(remainder, self.divisor // self.base)
            if (
                residue
                or u // 8 >= len(self.table)
                or not self.table[u // 8] & (1 << (u % 8))
            ):
                return None
            terms = []
            for k in range(len(self.base_denominators) - 1, -1, -1):
                if not (self.prefixes[k] >> u) & 1:
                    d = self.base_denominators[k]
                    terms.append(d)
                    u -= self.base // d
            assert u == 0
            return terms

        return visit(0, target)


def candidates(left, right, modulus):
    """Yield nearest nonzero residues of left+right in increasing distance."""
    nright = len(right)
    order = sorted(range(nright), key=lambda j: right[j] % modulus)
    residues = [right[j] % modulus for j in order]
    periodic = [r + shift for shift in (0, modulus, 2 * modulus) for r in residues]
    centers = [modulus + (-total) % modulus for total in left]
    heap = []
    for i, center in enumerate(centers):
        for j, step in (
            (bisect_left(periodic, center) - 1, -1),
            (bisect_right(periodic, center), 1),
        ):
            gap = abs(periodic[j] - center)
            if 0 < 2 * gap < modulus:
                heap.append((gap, i, j, step))
    heapify(heap)
    while heap:
        gap, i, j, step = heappop(heap)
        yield gap, i, order[j % nright]
        j += step
        if 0 <= j < len(periodic):
            gap = abs(periodic[j] - centers[i])
            if 0 < 2 * gap < modulus:
                heappush(heap, (gap, i, j, step))


def solve(n, cutoff, base):
    scale = lcm(*range(1, n + 1))
    divisor = lcm(base, *range(1, cutoff + 1))
    if scale % divisor:
        raise ValueError("the base and cutoff must divide the full common denominator")
    smooth = SmoothSums(n, divisor, base)
    rough = sorted(set(range(2, n + 1)) - smooth.denominators)
    midpoint = len(rough) // 2
    left = subset_totals(rough[:midpoint], scale)
    right = subset_totals(rough[midpoint:], scale)
    modulus = scale // divisor
    for gap, i, j in candidates(left, right, modulus):
        residual = scale - left[i] - right[j]
        target = (residual + modulus // 2) // modulus
        terms = smooth.represent(target)
        if terms is not None:
            terms += selected(rough[:midpoint], i) + selected(rough[midpoint:], j)
            error = sum((Fraction(1, d) for d in terms), Fraction(-1))
            assert abs(error) == Fraction(gap, scale)
            assert len(terms) == len(set(terms)) and max(terms) <= n
            # Including 1 gives either zero gap or a gap at least 1/N.
            if abs(error) >= Fraction(1, n):
                raise ValueError("need to account for subsets containing 1")
            return error, sorted(terms)
    raise ValueError("no gap below 1/(2D) found; choose a smaller cutoff or base")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("first", type=int)
    parser.add_argument("last", type=int, nargs="?")
    parser.add_argument("--cutoff", type=int, help="include lcm(1,...,cutoff) in D")
    parser.add_argument(
        "--base", type=int, default=27720, help="denominator for the bitset"
    )
    args = parser.parse_args()
    for n in range(args.first, (args.last or args.first) + 1):
        error, terms = solve(n, args.cutoff or n // 3, args.base)
        print(n, error, ",".join(map(str, terms)), sep="\t", flush=True)


if __name__ == "__main__":
    main()
