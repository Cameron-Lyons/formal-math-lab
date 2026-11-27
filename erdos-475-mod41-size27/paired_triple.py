"""Construct Graham orderings for sets omitting at most three nonzero residues.

Run --example P RESIDUES... for such a set, or for inverse pairs plus a
zero-sum triple. Run --through 257 to check normalized zero-sum triples
through 257 and all sets with at most three omissions at primes up to 43.
"""

from __future__ import annotations

import argparse
from itertools import accumulate, combinations, pairwise
from math import isqrt
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterable


def odd_prime(p: int) -> bool:
    return p >= 3 and p % 2 == 1 and all(p % d for d in range(3, isqrt(p) + 1, 2))


def validated_set(p: int, residues: Iterable[int]) -> set[int]:
    if p != 2 and not odd_prime(p):
        raise ValueError("the modulus must be prime")
    values = tuple(residues)
    elements = set(values)
    if len(elements) != len(values) or any(not 0 < x < p for x in elements):
        raise ValueError("provide distinct residues between 1 and p-1")
    return elements


def check_order(p: int, elements: set[int], order: tuple[int, ...]) -> None:
    if len(order) != len(elements) or set(order) != elements:
        raise ValueError("the output must use each input residue exactly once")
    partial_sums = {s % p for s in accumulate(order)}
    if len(partial_sums) != len(order):
        raise ValueError("the nonempty running sums must be distinct")


def folded_vertices(lengths: list[int]) -> list[int]:
    """Build a closed cycle for strictly decreasing positive lengths."""
    path = [0]
    for i, step in enumerate(lengths):
        path.append(path[-1] + (step if i % 2 == 0 else -step))
    return [*path, *(x - lengths[0] for x in reversed(path[1:]))]


def paired_triple_order(p: int, residues: Iterable[int]) -> tuple[int, ...]:
    """Return a checked ordering for distinct nonzero residues mod an odd prime.

    Exactly three residues must lack their negatives, and their sum must be zero.
    """
    elements = validated_set(p, residues)
    unmatched = sorted(x for x in elements if p - x not in elements)
    if len(unmatched) != 3 or sum(unmatched) % p:
        raise ValueError(
            "expected inverse pairs and three unmatched residues summing to 0"
        )

    # After scaling by a^{-1}, the other two residues sum to p-1 as integers.
    a = unmatched[0]
    scale = pow(a, -1, p)
    r = min(scale * x % p for x in unmatched[1:])
    length = r + 1
    normalized = {scale * x % p for x in elements}
    pair_lengths = [x for x in normalized if x < p - x and p - x in normalized]
    lengths = sorted([*pair_lengths, length], reverse=True)
    vertices = folded_vertices(lengths)
    edge = lengths.index(length)
    start, end = vertices[edge : edge + 2]
    if start < end:
        vertices.insert(edge + 1, start + 1)
    else:
        vertices.insert(edge + 1, start - 1)
        vertices.reverse()
    original_order = tuple(a * (v - u) % p for u, v in pairwise(vertices))
    check_order(p, elements, original_order)
    return original_order


def _dense_zero_sum_order(p: int, elements: set[int]) -> tuple[int, ...]:
    if any(p - x not in elements for x in elements):
        return paired_triple_order(p, elements)
    if not elements:
        return ()
    lengths = sorted((x for x in elements if x < p - x), reverse=True)
    return tuple((v - u) % p for u, v in pairwise(folded_vertices(lengths)))


def dense_order(p: int, residues: Iterable[int]) -> tuple[int, ...]:
    """Return a checked Graham ordering for any set omitting <=3 nonzero residues."""
    elements = validated_set(p, residues)
    if len(elements) < p - 4:
        raise ValueError("at most three nonzero residues may be omitted")
    total = sum(elements) % p
    if len(elements) <= 1:
        order = tuple(elements)
    elif total == 0:
        order = _dense_zero_sum_order(p, elements)
    else:
        extended = elements | {0}
        # Subtracting total visits the entire field, so some step leaves extended.
        a = next(x for x in extended if (x - total) % p not in extended)
        b = (a - total) % p
        cycle = _dense_zero_sum_order(p, (elements - {a}) | {b})
        index = cycle.index(b)
        order = cycle[index + 1 :] + cycle[:index]
        if a:
            order = (a, *order)
    check_order(p, elements, order)
    return order


def smoke_check(limit: int) -> None:
    dense = sparse = 0
    all_sets = 0
    dense_limit = min(limit, 43)
    for p in range(2, dense_limit + 1):
        if p != 2 and not odd_prime(p):
            continue
        full = set(range(1, p))
        for omitted in range(4):
            for missing in combinations(range(1, p), omitted):
                dense_order(p, full.difference(missing))
                all_sets += 1
    for p in range(7, limit + 1, 2):
        if not odd_prime(p):
            continue
        half = (p - 1) // 2
        for r in range(2, half):
            triple = (1, r, p - r - 1)
            available = [d for d in range(2, half + 1) if d not in (r, r + 1)]
            # For size p-4 all available pairs occur. Every zero-sum set
            # of that size has a zero-sum triple as its complement in F_p*.
            paired_triple_order(p, [*triple, *available, *(p - d for d in available)])
            dense += 1
            if p <= 23:
                for count in range(len(available)):
                    for choice in combinations(available, count):
                        # Test the return from normalized to original coordinates, too.
                        values = [*triple, *choice, *(p - d for d in choice)]
                        paired_triple_order(p, (2 * x % p for x in values))
                        sparse += 1
    print(f"Checked {dense} normalized dense cases and {sparse} sparse cases.")
    print(f"Checked all {all_sets} dense sets at primes up to {dense_limit}.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--through", type=int, default=257, metavar="LIMIT")
    mode.add_argument("--example", type=int, nargs="+", metavar="NUMBER")
    args = parser.parse_args()
    if args.example is None:
        smoke_check(args.through)
    else:
        p, *residues = args.example
        construct = dense_order if len(residues) >= p - 4 else paired_triple_order
        print(*construct(p, residues))


if __name__ == "__main__":
    main()
