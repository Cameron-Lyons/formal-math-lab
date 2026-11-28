"""Sharp reflection bounds with one transposed color pair and any number of fixed colors."""

from itertools import product


def progressions(n):
    return [
        (a, a + d, a + 2 * d, a + 3 * d)
        for d in range(1, (n - 1) // 3 + 1)
        for a in range(n - 3 * d)
    ]


def color(n, position, states):
    i = min(position, n - 1 - position)
    state = states[i]
    if state == 0:
        return 2 + i  # Give each fixed pair its own color.
    return (state - 1) ^ int(2 * position >= n)


def constraint_tables(n):
    # Group progressions that involve the same variables on the half-interval.
    forbidden = {}
    for ap in progressions(n):
        indices = tuple(sorted({min(i, n - 1 - i) for i in ap}))
        bad = forbidden.setdefault(indices, set())
        for choices in product(range(3), repeat=len(indices)):
            states = dict(zip(indices, choices, strict=True))
            if len({color(n, i, states) for i in ap}) < 3:
                bad.add(choices)
    tables = []
    for indices, bad in forbidden.items():
        allowed = [
            row for row in product(range(3), repeat=len(indices)) if row not in bad
        ]
        if not bad:
            continue
        # Bit k of table[j][mask] says whether row k has an allowed state at j.
        table = [
            [
                sum(1 << k for k, row in enumerate(allowed) if mask & (1 << row[j]))
                for mask in range(8)
            ]
            for j in range(len(indices))
        ]
        tables.append((indices, table))
    return tables


def solve(n):
    half = (n + 1) // 2
    tables = constraint_tables(n)
    incident = [[] for _ in range(half)]
    for j, (indices, _) in enumerate(tables):
        for i in indices:
            incident[i].append(j)
    nodes = 0

    def search(domains, queue):
        nonlocal nodes
        nodes += 1
        while queue:
            v = queue.pop()
            for j in incident[v]:
                indices, table = tables[j]
                possible = -1
                for i, masks in zip(indices, table, strict=True):
                    possible &= masks[domains[i]]
                if not possible:
                    return None
                for i, masks in zip(indices, table, strict=True):
                    supported = sum(bit for bit in (1, 2, 4) if masks[bit] & possible)
                    if supported != domains[i]:
                        domains[i] = supported
                        queue.append(i)
        free = [i for i in range(half) if domains[i].bit_count() > 1]
        if not free:
            return [mask.bit_length() - 1 for mask in domains]
        i = min(free, key=lambda k: (domains[k].bit_count(), -len(incident[k])))
        for bit in (1, 2, 4):
            if domains[i] & bit:
                child = domains.copy()
                child[i] = bit
                witness = search(child, [i])
                if witness is not None:
                    return witness
        return None

    domains = [7] * half
    domains[0] = 3  # Exchange the two moving color names if necessary.
    if n % 2:
        domains[-1] = 1
    states = search(domains, list(range(half)))
    if states is not None:
        for ap in progressions(n):
            if len({color(n, i, states) for i in ap}) < 3:
                raise ValueError("invalid witness")
    return states, nodes


if __name__ == "__main__":
    for n, expected in ((44, True), (46, False), (65, True), (67, False)):
        states, nodes = solve(n)
        if (states is not None) != expected:
            raise ValueError(f"unexpected result at {n}")
        print(
            f"N={n} nodes={nodes} half-word="
            + ("none" if states is None else "".join(map(str, states)))
        )
