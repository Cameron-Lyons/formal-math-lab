"""Search for expansions without any power-of-two cycle.

Run `python scripts/gadget_csp.py /path/to/geng` with nauty 2.9.3. The
second and third positional arguments optionally set the largest cubic and
two-defect base orders, respectively. A witness, if found, assigns a label
to every vertex, in the order returned by library().
"""

import argparse
import subprocess
from functools import cache

from mixed_gadget_graph import PORTS, gadget, path_lengths, short_cycles


def has_power(low, high):
    """Test inclusion of 4, 8, 16, ... in the integer interval [low, high]."""
    return max(4, 1 << (low - 1).bit_length()) <= high


def oriented_pieces():
    """Index oriented pieces by their three transit intervals including one base edge."""
    symmetric = [[4, 5, 6], [2, 3, 4], [1, 3, 5], [1, 2, 6], [0, 1], [0, 2], [0, 3]]
    triangle = [[1, 2], [0, 2], [0, 1]]
    # H7' is a K4 with all three edges incident to one vertex subdivided once.
    pieces = [
        (triangle, (0, 1, 2)),
        (gadget(7), PORTS[7]),
        (symmetric, (4, 5, 6)),
        (gadget(15), PORTS[15]),
    ]
    models = {((1, 1),) * 3: ([[]], (0, 0, 0))}  # Leave the vertex unchanged.
    for graph, ports in pieces:
        if any(has_power(len(c), len(c)) for c in short_cycles(graph, len(graph))):
            raise ValueError("A library piece has an internal dyadic cycle")
        transits = []
        for i in range(3):
            paths = path_lengths(graph, ports[(i + 1) % 3], ports[(i + 2) % 3])
            lo, hi = min(paths), max(paths)
            if len(paths) != hi - lo + 1:
                raise ValueError("A transit set is not an interval")
            transits.append((1 + lo, 1 + hi))
        # In H7 and H15 port 0 is distinguished. Both other ports have
        # identical transit spectra, so the three rotations cover all bijections.
        if transits[1] != transits[2]:
            raise ValueError("Uncovered orientation")
        for i in range(3):
            label = tuple(transits[i:] + transits[:i])
            models.setdefault(label, (graph, ports[i:] + ports[:i]))
    return models


def library():
    return list(oriented_pieces())


def decode(line):
    """Decode short graph6, whose adjacency bits are ordered by the higher endpoint."""
    n = line[0] - 63
    if not (0 < n < 63) or len(line) != 1 + (n * (n - 1) + 11) // 12:
        raise ValueError("Expected single-byte-order graph6")
    graph = [[] for _ in range(n)]
    for v in range(n):
        for u in range(v):
            i = v * (v - 1) // 2 + u
            if (line[1 + i // 6] - 63) & (32 >> (i % 6)):
                graph[u].append(v)
                graph[v].append(u)
    return graph


def completion_test(labels, maximum=None):
    # Only one base cycle is under consideration here. At each fixed upper
    # endpoint, maximizing the lower endpoint makes avoiding powers easiest.
    lower_for_upper = {}
    for label in labels:
        for low, high in label:
            lower_for_upper[high] = max(low, lower_for_upper.get(high, low))
    maximal = [(low, high) for high, low in lower_for_upper.items()]

    @cache
    def possible(remaining, low, high):
        if remaining == 0:
            return not has_power(low, high if maximum is None else min(high, maximum))
        return any(possible(remaining - 1, low + a, high + b) for a, b in maximal)

    return possible


def clean_assignments(graph, labels, possible):
    # Each crossing cycle uses two boundary edges per visited piece and
    # projects to a simple base cycle. Every integer in the sum of the local
    # intervals is realized by independently choosing a path in each piece.
    incidents = [[] for _ in graph]
    remaining = []
    for cycle in short_cycles(graph, len(graph)):
        index = len(remaining)
        remaining.append(len(cycle))
        for i, v in enumerate(cycle):
            left = graph[v].index(cycle[i - 1])
            right = graph[v].index(cycle[(i + 1) % len(cycle)])
            # At a degree-two vertex the unattached port receives index 2.
            incidents[v].append((index, 3 - left - right))
    low = [0] * len(remaining)
    high = [0] * len(remaining)
    assignment = [-1] * len(graph)

    def allowed(v, label):
        for i, omitted in incidents[v]:
            a, b = label[omitted]
            if not possible(remaining[i] - 1, low[i] + a, high[i] + b):
                return False
        return True

    def apply(v, label, sign):
        for i, omitted in incidents[v]:
            a, b = label[omitted]
            low[i] += sign * a
            high[i] += sign * b
            remaining[i] -= sign

    def search():
        best = None
        for v, selected in enumerate(assignment):
            if selected >= 0:
                continue
            domain = [s for s, label in enumerate(labels) if allowed(v, label)]
            if not domain:
                return
            score = len(domain), -len(incidents[v])
            if best is None or score < best[0]:
                best = score, v, domain
        if best is None:
            yield tuple(assignment)
            return
        _, v, domain = best
        for s in domain:
            assignment[v] = s
            apply(v, labels[s], 1)
            yield from search()
            apply(v, labels[s], -1)
            assignment[v] = -1

    yield from search()


def generate_bases(geng, order, defects):
    if order >= 63 or (3 * order - defects) % 2:
        raise ValueError("Unsupported graph6 order or impossible degree sum")
    edges = (3 * order - defects) // 2
    command = [geng, "-cqd2D3", str(order), f"{edges}:{edges}"]
    return subprocess.run(command, check=True, capture_output=True).stdout.splitlines()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("geng", nargs="?", default="geng")
    parser.add_argument("cubic_max", nargs="?", type=int, default=14)
    parser.add_argument("two_defect_max", nargs="?", type=int, default=12)
    args = parser.parse_args()
    labels = library()
    possible = completion_test(labels)
    print(f"{len(labels)} distinct oriented labels")
    for defects, limit in ((0, args.cubic_max), (2, args.two_defect_max)):
        for n in range(4, limit + 1, 2):
            clean = 0
            bases = generate_bases(args.geng, n, defects)
            for line in bases:
                assignment = next(
                    clean_assignments(decode(line), labels, possible), None
                )
                if assignment is not None:
                    clean += 1
                    print(line.decode(), assignment)
            print(
                f"degree-two vertices={defects} order={n} bases={len(bases)} bases with clean expansion={clean}",
                flush=True,
            )


if __name__ == "__main__":
    main()
