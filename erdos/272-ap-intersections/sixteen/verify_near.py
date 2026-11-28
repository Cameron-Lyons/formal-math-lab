"""Exclude a 125-member family on [16] in which some point is omitted at most R times.

Use Python 3.10 or later. Run python3 verify_near.py [R]. The point-dependent
star bound is checked by matching large progressions to omitted triples.
Points are numbered 0 through 15.
"""

import sys
from functools import cache
from itertools import combinations
from math import gcd

POINTS = 16
LIMIT = 1 << POINTS
FULL = LIMIT - 1
TARGET = 125


def progressions():
    result = set()
    for first in range(POINTS):
        for step in range(1, POINTS):
            mask = 0
            for point in range(first, POINTS, step):
                mask |= 1 << point
                result.add(mask)
    return result


AP = progressions()


def verify_star_bound(point):
    """Cover the star with at most 121 + floor(point/2) independent classes."""
    center = 1 << point
    hulls = {}
    for a, b, c in combinations(range(POINTS), 3):
        triple = (1 << a) | (1 << b) | (1 << c)
        if not triple & center or triple in AP:
            continue
        step = gcd(b - a, c - b)
        hulls[triple] = sum(1 << i for i in range(a, c + 1, step))

    for mask in range(1, LIMIT):
        if not mask & center or mask.bit_count() < 4 or mask in AP:
            continue
        if not any(
            mask & triple == triple and mask & hull != hull
            for triple, hull in hulls.items()
        ):
            raise RuntimeError(f"No incompatible triple for {mask} at {point}")

    large = sorted(p for p in AP if p & center and p.bit_count() >= 4)
    triples_in = {p: [t for t in hulls if p & t == t] for p in large}
    matched = {}

    def augment(progression, visited):
        for triple in triples_in[progression]:
            if triple in visited:
                continue
            visited.add(triple)
            if triple not in matched or augment(matched[triple], visited):
                matched[triple] = progression
                return True
        return False

    for progression in large:
        augment(progression, set())
    if len(large) - len(matched) > point // 2:
        raise RuntimeError(f"Too many unmatched progressions at {point}")


def bit_indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def submasks(mask):
    current = mask
    while True:
        yield current
        if not current:
            break
        current = (current - 1) & mask


@cache
def compatible_with(mask):
    # The index of a bit in this bitmap is itself a subset of [16].
    result = bytearray(LIMIT // 8)
    for candidate in range(1, LIMIT):
        if (candidate & mask) in AP:
            result[candidate // 8] |= 1 << (candidate % 8)
    return int.from_bytes(result, "little")


@cache
def through(point):
    result = bytearray(LIMIT // 8)
    for mask in range(1, LIMIT):
        if mask & (1 << point):
            result[mask // 8] |= 1 << (mask % 8)
    return int.from_bytes(result, "little")


def cliques_of_size(masks, size):
    if len(masks) < size:
        return
    neighbors = [
        sum(1 << j for j, other in enumerate(masks) if i != j and (mask & other) in AP)
        for i, mask in enumerate(masks)
    ]

    def visit(candidates, needed, chosen):
        if needed == 0:
            yield tuple(chosen)
            return
        if candidates.bit_count() < needed:
            return
        # Each color class is an independent set. A clique in the prefix of
        # the order ending at color c can contain at most c vertices.
        order = []
        bounds = []
        remaining = candidates
        color = 0
        while remaining:
            color += 1
            available = remaining
            while available:
                bit = available & -available
                i = bit.bit_length() - 1
                available &= ~(bit | neighbors[i])
                remaining ^= bit
                order.append(i)
                bounds.append(color)
        for i, bound in zip(reversed(order), reversed(bounds), strict=True):
            if bound < needed:
                return
            chosen.append(masks[i])
            yield from visit(candidates & neighbors[i], needed - 1, chosen)
            chosen.pop()
            candidates ^= 1 << i

    yield from visit((1 << len(masks)) - 1, size, [])


def verify(omissions):
    profiles = 0
    tested = set()
    checked_stars = set()
    for point in range(POINTS // 2):
        # Reflection handles the other eight choices of point.
        x = 1 << point
        for core in sorted(AP | {0}):
            if core & x:
                continue
            outside = FULL ^ core ^ x
            slack = omissions - outside.bit_count() - 5 + point // 2
            if slack < 0 or (1 << outside.bit_count()) < omissions:
                continue
            # Each omitted set contains the core. If it misses both of the
            # other points of a progression triple through x, that triple
            # can be added back to the star. At most slack such triples exist.
            pairs = sorted(
                t ^ x for t in AP if t.bit_count() == 3 and t & x and not t & core
            )
            supersets = [core | t for t in submasks(outside)]
            for missing_pairs in combinations(pairs, min(len(pairs), slack)):
                required = set(pairs).difference(missing_pairs)
                possible = [s for s in supersets if all(s & p for p in required)]
                profiles += 1
                for omitted in cliques_of_size(possible, omissions):
                    common = FULL
                    for mask in omitted:
                        common &= mask
                    if common != core:
                        continue
                    key = (point, tuple(sorted(omitted)))
                    if key in tested:
                        continue
                    tested.add(key)
                    star = through(point)
                    for mask in omitted:
                        star &= compatible_with(mask)
                    if star in checked_stars:
                        continue
                    checked_stars.add(star)
                    needed = TARGET - omissions
                    if star.bit_count() >= needed:
                        witness = next(
                            cliques_of_size(list(bit_indices(star)), needed), None
                        )
                        if witness is not None:
                            raise RuntimeError(
                                f"125-member family: {omitted + witness}"
                            )
    return profiles, len(tested), len(checked_stars)


if __name__ == "__main__":
    bound = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    if not 2 <= bound < TARGET:
        raise SystemExit("Supply a maximum between 2 and 124.")
    for point in range(POINTS // 2):
        verify_star_bound(point)
    # No omissions is covered by the star bound. One omission contradicts
    # r >= m + 5 - floor(point/2) even before using that the core is an AP.
    for count in range(2, bound + 1):
        profiles, families, stars = verify(count)
        print(
            f"{count} omissions: {profiles} profiles, {families} omitted families, "
            f"{stars} distinct lists of retained members",
            flush=True,
        )
