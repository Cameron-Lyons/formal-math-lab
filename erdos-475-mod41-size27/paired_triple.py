"""Construct Graham orderings for sets omitting at most four nonzero residues.

Run --example P RESIDUES... for such a set, or for inverse pairs plus a
zero-sum triple or quartet. Run --through 257 to check normalized cases
through 257 and all sets with at most four omissions at primes up to 43.
"""

from __future__ import annotations

import argparse
from itertools import accumulate, combinations
from math import isqrt
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable


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


def _fold_steps(positive: list[int], negative: list[int]) -> list[int]:
    """Take alternating signs from decreasing pairs, then their unused steps."""
    first, unused = [], []
    for i, (r, s) in enumerate(zip(positive, negative, strict=True)):
        step, mate = (r, -s) if i % 2 == 0 else (-s, r)
        first.append(step)
        unused.append(mate)
    # Take the largest pair's unused step, then the others smallest pair first.
    return [*first, *unused[:1], *reversed(unused[1:])]


def folded_vertices(
    lengths: list[int], negative_lengths: list[int] | None = None
) -> list[int]:
    """Return cycle vertices for decreasing pairs of equal total magnitudes."""
    if negative_lengths is None:
        negative_lengths = lengths
    return list(accumulate(_fold_steps(lengths, negative_lengths), initial=0))


def _dense_zero_sum_order(
    p: int, elements: set[int], allowed_counts: tuple[int, ...] = (0, 3, 4)
) -> tuple[int, ...]:
    unmatched = sorted(x for x in elements if p - x not in elements)
    if len(unmatched) not in allowed_counts or sum(unmatched) % p:
        raise ValueError(
            f"expected unmatched residues of sum zero and count in {allowed_counts}"
        )

    # Scale two unmatched steps to have sum +1, leaving sum -1 for the rest.
    unit = (unmatched[0] + unmatched[1]) % p if unmatched else 1
    scale = pow(unit, -1, p)
    normalized = {scale * x % p for x in elements}
    # Each pair occupies one magnitude or two consecutive magnitudes.
    # Sorting both signs by magnitude therefore lines up their partners.
    positive = sorted((x for x in normalized if x <= p // 2), reverse=True)
    negative = sorted((p - x for x in normalized if x > p // 2), reverse=True)
    if len(unmatched) == 3:
        positive.append(0)  # The last pair is (0, -1). Drop the dummy step below.
    order = tuple(unit * x % p for x in _fold_steps(positive, negative) if x)
    check_order(p, elements, order)
    return order


def paired_triple_order(p: int, residues: Iterable[int]) -> tuple[int, ...]:
    """Return a checked ordering for inverse pairs and a zero-sum unmatched triple."""
    return _dense_zero_sum_order(p, validated_set(p, residues), (3,))


def paired_quartet_order(p: int, residues: Iterable[int]) -> tuple[int, ...]:
    """Return a checked ordering for inverse pairs and a zero-sum unmatched quartet."""
    return _dense_zero_sum_order(p, validated_set(p, residues), (4,))


def dense_order(p: int, residues: Iterable[int]) -> tuple[int, ...]:
    """Return a checked Graham ordering for any set omitting <=4 nonzero residues."""
    elements = validated_set(p, residues)
    if len(elements) < p - 5:
        raise ValueError("at most four nonzero residues may be omitted")
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


def _check_pair_choices(
    p: int,
    unmatched: tuple[int, ...],
    construct: Callable[[int, Iterable[int]], tuple[int, ...]],
) -> int:
    occupied = {min(x, p - x) for x in unmatched}
    available = [d for d in range(1, p // 2 + 1) if d not in occupied]
    construct(p, [*unmatched, *available, *(p - d for d in available)])
    sparse = 0
    if p <= 23:
        for count in range(len(available)):
            for choice in combinations(available, count):
                values = [*unmatched, *choice, *(p - d for d in choice)]
                # Exercise the return from normalized to original coordinates.
                construct(p, (2 * x % p for x in values))
                sparse += 1
    return sparse


def smoke_check(limit: int) -> None:
    dense_triples = sparse_triples = 0
    dense_quartets = sparse_quartets = 0
    all_sets = 0
    dense_limit = min(limit, 43)
    for p in range(2, dense_limit + 1):
        if p != 2 and not odd_prime(p):
            continue
        full = set(range(1, p))
        for omitted in range(5):
            for missing in combinations(range(1, p), omitted):
                dense_order(p, full.difference(missing))
                all_sets += 1
    for p in range(7, limit + 1, 2):
        if not odd_prime(p):
            continue
        half = (p - 1) // 2
        for r in range(2, half):
            triple = (1, r, p - r - 1)
            sparse_triples += _check_pair_choices(p, triple, paired_triple_order)
            dense_triples += 1
        # Up to simultaneous negation, the slot with sum +1 has the
        # smaller magnitudes. The two adjacent magnitude intervals are disjoint.
        for r in range(1, half):
            for s in range(r + 2, half):
                quartet = (r + 1, p - r, s, p - s - 1)
                sparse_quartets += _check_pair_choices(p, quartet, paired_quartet_order)
                dense_quartets += 1
    print(
        f"Checked {dense_triples} normalized dense triples and {sparse_triples} sparse triples."
    )
    print(
        f"Checked {dense_quartets} normalized dense quartets and {sparse_quartets} sparse quartets."
    )
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
        if len(residues) >= p - 5:
            order = dense_order(p, residues)
        else:
            order = _dense_zero_sum_order(p, validated_set(p, residues))
        print(*order)


if __name__ == "__main__":
    main()
