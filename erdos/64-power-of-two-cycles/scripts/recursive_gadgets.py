"""Verify closure under arbitrary-depth replacement by small three-port graphs.

Run `python scripts/recursive_gadgets.py /path/to/geng` with nauty 2.9.3.
The second argument can lower the three-port core order bound for a quick run.
"""

import argparse

from gadget_csp import (
    clean_assignments,
    completion_test,
    decode,
    generate_bases,
    has_power,
    oriented_pieces,
)
from mixed_gadget_graph import short_cycles


def expand(graph, pieces):
    """Instantiate a tuple of oriented pieces, assigning half-edges in neighbor order."""
    result = []
    ports = []
    for piece, attachments in pieces:
        offset = len(result)
        ports.append([offset + p for p in attachments])
        result.extend([offset + w for w in neighbors] for neighbors in piece)
    for v, neighbors in enumerate(graph):
        for i, w in enumerate(neighbors):
            result[ports[v][i]].append(ports[w][graph[w].index(v)])
    return result


def isomorphic(graph, model):
    """Complete adjacency-preserving bijection search; all three ports have degree two."""
    if len(graph) != len(model):
        return False
    n = len(graph)
    assignment = {}

    def visit():
        if len(assignment) == n:
            return True
        remaining = [v for v in range(n) if v not in assignment]
        v = max(remaining, key=lambda x: sum(w in assignment for w in graph[x]))
        for y, neighbors in enumerate(model):
            if y in assignment.values() or len(neighbors) != len(graph[v]):
                continue
            if all((w in graph[v]) == (z in neighbors) for w, z in assignment.items()):
                assignment[v] = y
                if visit():
                    return True
                del assignment[v]
        return False

    return visit()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("geng", nargs="?", default="geng")
    parser.add_argument("core_max", nargs="?", type=int, default=13)
    args = parser.parse_args()
    models = oriented_pieces()
    labels = list(models)
    pieces = list(models.values())
    representatives = [
        piece
        for i, (piece, _) in enumerate(pieces)
        if not any(isomorphic(piece, previous) for previous, _ in pieces[:i])
    ]
    if len(labels) != 9 or len(representatives) != 5:
        raise ValueError("Unexpected oriented gadget library")
    expected_transitions = {
        3: (1, 7),
        5: (2, 6),
        7: (10, 5),
        9: (63, 4),
        11: (482, 4),
        13: (4541, 2),
    }
    possible = completion_test(labels, maximum=32)
    for order in range(3, args.core_max + 1, 2):
        bases = generate_bases(args.geng, order, 3)
        clean = 0
        max_order = 0
        for line in bases:
            graph = decode(line)
            for indices in clean_assignments(graph, labels, possible):
                expanded = expand(graph, [pieces[i] for i in indices])
                if not any(isomorphic(expanded, model) for model in representatives):
                    raise ValueError(
                        f"New clean piece: core {line!r}, assignment {indices}"
                    )
                if any(
                    has_power(len(c), len(c))
                    for c in short_cycles(expanded, len(expanded))
                ):
                    raise ValueError(
                        f"False survivor: core {line!r}, assignment {indices}"
                    )
                clean += 1
                max_order = max(max_order, len(expanded))
        if (
            order in expected_transitions
            and (len(bases), clean) != expected_transitions[order]
        ):
            raise ValueError(f"Transition count mismatch at order {order}")
        print(
            f"three-port order={order} bases={len(bases)} clean assignments={clean} maximum expanded order={max_order}",
            flush=True,
        )
    for defects, counts in ((0, (1, 2, 5, 19, 85, 509)), (2, (1, 4, 19))):
        for index, expected in enumerate(counts):
            order = 4 + 2 * index
            bases = generate_bases(args.geng, order, defects)
            if len(bases) != expected:
                raise ValueError(
                    f"Root count mismatch at order {order} and defect {defects}"
                )
            for line in bases:
                result = next(clean_assignments(decode(line), labels, possible), None)
                if result is not None:
                    raise ValueError(
                        f"Clean root expansion: core {line!r}, assignment {result}"
                    )
            print(
                f"degree-two vertices={defects} order={order} bases={len(bases)} clean assignments=0",
                flush=True,
            )


if __name__ == "__main__":
    main()
