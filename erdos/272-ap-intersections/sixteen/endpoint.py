"""Check the duplicate-pair bound used in endpoint.md. Run with Python 3.10+."""

from functools import cache

N = 16
LIMIT = 1 << N
FULL_DOMAIN = (1 << LIMIT) - 1
TARGET = 125
DUPLICATES = 12
OMISSIONS = 14  # proved independently by verify_near.py


def progressions():
    result = set()
    for first in range(N):
        for step in range(1, N):
            mask = 0
            for point in range(first, N, step):
                mask |= 1 << point
                result.add(mask)
    return result


AP = progressions()


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def bitmap(masks):
    data = bytearray(LIMIT // 8)
    for mask in masks:
        data[mask // 8] |= 1 << (mask % 8)
    return int.from_bytes(data, "little")


def maximal_collections(required):
    """Maximal cliques of possible duplicate bases, numbered by their masks."""
    bases = sorted(p for p in AP if not p & 1)

    def compatible(p, q):
        trace = p & q
        return p != q and trace in AP and (trace | 1) in AP

    degrees = {p: sum(compatible(p, q) for q in bases) for p in bases}
    bases.sort(key=lambda p: -degrees[p])
    neighbors = [
        sum(1 << j for j, q in enumerate(bases) if compatible(p, q)) for p in bases
    ]

    def visit(possible, excluded, chosen):
        if len(chosen) + possible.bit_count() < required:
            return
        if not possible:
            if not excluded:
                yield tuple(bases[i] for i in chosen)
            return
        # A maximal extension must use the pivot or one of its nonneighbors.
        pivot = max(
            indices(possible | excluded),
            key=lambda i: (possible & neighbors[i]).bit_count(),
        )
        for i in indices(possible & ~neighbors[pivot]):
            yield from visit(
                possible & neighbors[i], excluded & neighbors[i], [*chosen, i]
            )
            possible ^= 1 << i
            excluded |= 1 << i

    yield from visit((1 << len(bases)) - 1, 0, [])


@cache
def allowed_with(base):
    """Masks that can coexist with both the base and its endpoint extension."""
    enlarged = base | 1
    return bitmap(
        a
        for a in range(1, LIMIT)
        if (a & base) in AP and (a == enlarged or (a & enlarged) in AP)
    )


def at_most_failures(bases, limit):
    layers = [FULL_DOMAIN] * (limit + 1)
    for base in bases:
        allowed = allowed_with(base)
        # Layer j permits failure against at most j of the bases seen so far.
        for j in range(limit, 0, -1):
            layers[j] = (layers[j] & allowed) | layers[j - 1]
        layers[0] &= allowed
    return layers[-1]


def ordering():
    # Sort by the number of subsets giving a progression as intersection.
    count = [int(a in AP) for a in range(LIMIT)]
    for i in range(N):
        bit = 1 << i
        for start in range(bit, LIMIT, 2 * bit):
            for a in range(start, start + bit):
                count[a] += count[a - bit]
    return sorted(
        range(1, LIMIT), key=lambda a: (-count[a] * (1 << (N - a.bit_count())), -a)
    )


def enough_colors(masks, needed):
    colors = []
    for a in masks:
        for group in colors:
            if all((a & b) not in AP for b in group):
                group.append(a)
                break
        else:
            colors.append([a])
            if len(colors) == needed:
                return True
    return False


def verify():
    rank = {a: i for i, a in enumerate(ordering())}
    omitted = [bitmap(a for a in range(1, LIMIT) if not a & (1 << i)) for i in range(N)]
    vertices = bitmap(a for a in range(1, LIMIT) if a.bit_count() >= 2)

    def possible(domain):
        if domain.bit_count() < TARGET:
            return False
        for outside in sorted((domain & mask for mask in omitted), key=int.bit_count):
            if outside.bit_count() < OMISSIONS:
                return False
            # The cutoff only skips an optional upper bound on large domains.
            if outside.bit_count() < 300:
                candidates = sorted(indices(outside), key=rank.__getitem__)
                if not enough_colors(candidates, OMISSIONS):
                    return False
        candidates = sorted(indices(domain), key=rank.__getitem__)
        return enough_colors(candidates, TARGET) and enough_colors(
            reversed(candidates), TARGET
        )

    def uncovered(candidates, required):
        # After taking required - 1 independent classes, any clique of the
        # required size must contain one of the remaining masks.
        groups = []
        tail = []
        for a in candidates:
            for group in groups:
                if all((a & b) not in AP for b in group):
                    group.append(a)
                    break
            else:
                if len(groups) < required - 1:
                    groups.append([a])
                else:
                    tail.append(a)
        return tail

    def extension_possible(candidates, needed, omissions, depth):
        if len(candidates) < needed:
            return False
        branch = candidates
        for point, required in enumerate(omissions):
            if required <= 0:
                continue
            outside = [a for a in candidates if not a & (1 << point)]
            if len(outside) < required:
                return False
            if len(outside) <= 1000:
                tail = uncovered(outside, required)
                if not tail:
                    return False
                if len(tail) < len(branch):
                    branch = tail
        if not enough_colors(candidates, needed) or not enough_colors(
            reversed(candidates), needed
        ):
            return False
        if depth == 0:
            return True
        available = set(candidates)
        for a in branch:
            available.remove(a)
            neighbors = [b for b in candidates if b in available and (a & b) in AP]
            remaining = [
                count - int(not (a & (1 << i))) for i, count in enumerate(omissions)
            ]
            if extension_possible(neighbors, needed - 1, remaining, depth - 1):
                return True
        return False

    def check(undecided, domain, spare, fixed):
        nonlocal nodes
        nodes += 1
        allowed = domain & at_most_failures(undecided, spare)
        if not possible(allowed):
            return
        if spare == 0 or not undecided:
            roots = {a for p in fixed + undecided for a in (p, p | 1)}
            if any(a.bit_count() == 1 for a in roots):
                return
            candidates = sorted(
                (a for a in indices(allowed) if a not in roots), key=rank.__getitem__
            )
            required = [
                OMISSIONS - sum(not (a & (1 << i)) for a in roots) for i in range(N)
            ]
            if extension_possible(candidates, TARGET - len(roots), required, 3):
                raise ValueError(f"Unexcluded duplicate bases: {fixed + undecided}")
            return
        pivot = min(undecided, key=lambda p: (allowed_with(p) & allowed).bit_count())
        rest = tuple(p for p in undecided if p != pivot)
        check(rest, domain & allowed_with(pivot), spare, (*fixed, pivot))
        check(rest, domain, spare - 1, fixed)

    collections = nodes = 0
    for bases in maximal_collections(DUPLICATES):
        collections += 1
        check(bases, vertices, len(bases) - DUPLICATES, ())
    print(
        f"{collections} maximal collections, {nodes} branches. "
        f"Fewer than {DUPLICATES} duplicate pairs at either endpoint."
    )


if __name__ == "__main__":
    verify()
