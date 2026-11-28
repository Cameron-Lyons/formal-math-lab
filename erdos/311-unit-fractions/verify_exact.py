"""Verify upper and lower bounds in exact_gaps.tsv, without importing the search."""

from __future__ import annotations

import argparse
from bisect import bisect_left, bisect_right
from fractions import Fraction
from math import isqrt, lcm
from pathlib import Path


def sums(weights):
    values = [0]
    for weight in weights:
        values = values + [weight + x for x in values]
    return values


def smooth_oracle(n, scale):
    """Test exact membership by peeling one power of one prime per step."""
    denominators = [i for i in range(2, n + 1) if scale % i == 0]
    layers = []
    while scale > 100_000:
        # For each p | scale, only d with scale/d nonzero mod p can
        # influence the residue. Enumerate the smallest such group.
        candidates = []
        for p in range(2, n + 1):
            if scale % p == 0 and all(p % q for q in range(2, isqrt(p) + 1)):
                group = [d for d in denominators if (scale // d) % p != 0]
                candidates.append((len(group), p, group))
        _, p, group = min(candidates)
        by_residue = [[] for _ in range(p)]
        for v in sorted(set(sums([scale // d for d in group]))):
            by_residue[v % p].append(v)
        layers.append((p, by_residue))
        scale //= p
        denominators = [d for d in denominators if d not in group]

    bits = 1
    for d in denominators:
        bits |= bits << (scale // d)
    bitmap = bits.to_bytes((bits.bit_length() + 7) // 8, "little")

    def feasible(target, level=0):
        if target < 0:
            return False
        if level == len(layers):
            return target // 8 < len(bitmap) and bool(
                bitmap[target // 8] & (1 << (target % 8))
            )
        p, possible = layers[level]
        return any(feasible((target - v) // p, level + 1) for v in possible[target % p])

    return feasible


def exclude_smaller(n, upper):
    scale = lcm(*range(1, n + 1))
    # Smaller divisors mean longer outer lists. Larger divisors mean more
    # matches to check. The score selects a workload, never a proof cutoff.
    divisors = {lcm(*range(1, k + 1)) for k in range(n // 4, n // 2 + 1)}
    admissible = [d for d in divisors if 2 * upper * d < 1]

    def estimated_work(d):
        rough_count = sum(d % k != 0 for k in range(2, n + 1))
        list_length = 1 << ((rough_count + 1) // 2)
        expected_hits = 2 * upper * d * (1 << rough_count)
        return list_length * rough_count + 30 * expected_hits

    divisor = min(admissible, key=lambda d: (estimated_work(d), d))
    unit = scale // divisor
    digits = upper * scale
    assert digits.denominator == 1 and 0 < upper < Fraction(1, n)
    bound = int(digits)
    values = [scale // d for d in range(2, n + 1) if divisor % d]
    left = set(sums(values[::2]))
    right = sorted(set(sums(values[1::2])), key=lambda v: v % unit)
    residues = [v % unit for v in right]
    attainable = smooth_oracle(n, divisor)
    checked = 0
    for x in left:
        center = (-x) % unit
        for shift in (-unit, 0, unit):
            c = center + shift
            lo = bisect_right(residues, c - bound)
            hi = bisect_left(residues, c + bound)
            for i in range(lo, hi):
                signed = residues[i] - c
                if signed == 0:
                    continue
                # x + right[i] - signed is the multiple of unit nearest
                # x + right[i], with distance strictly less than bound.
                target, rem = divmod(scale - x - right[i] + signed, unit)
                assert rem == 0
                if attainable(target):
                    raise AssertionError(f"smaller nonzero gap at N={n}")
                checked += 1
    return checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--through", type=int, help="check only rows ending at or below N"
    )
    args = parser.parse_args()
    rows = Path(__file__).with_name("exact_gaps.tsv").read_text().splitlines()
    if rows[0] != "first_N\tlast_N\twitness_sum_minus_one\tdenominators":
        raise ValueError("unexpected table header")
    assert int(rows[1].split("\t")[0]) == 58 and int(rows[-1].split("\t")[1]) == 200
    previous_last = None
    previous_gap = None
    total = 0
    for row in rows[1:]:
        first, last, signed, values = row.split("\t")
        start, stop = int(first), int(last)
        if args.through is not None and stop > args.through:
            break
        ds = [int(d) for d in values.split(",")]
        assert 1 <= start <= stop
        assert previous_last is None or previous_last + 1 == start
        assert ds == sorted(set(ds)) and 1 <= min(ds) <= max(ds) <= start
        witness_error = sum((Fraction(1, d) for d in ds), Fraction(-1))
        assert witness_error == Fraction(signed)
        gap = abs(witness_error)
        assert previous_gap is None or 0 < gap < previous_gap
        total += exclude_smaller(stop, gap)
        print(f"certified {start}..{stop}: {gap}", flush=True)
        previous_last, previous_gap = stop, gap
    print(f"{total} strict-window candidates rejected by integer feasibility.")


if __name__ == "__main__":
    main()
