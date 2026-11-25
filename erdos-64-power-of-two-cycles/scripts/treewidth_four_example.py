"""Check the width-four example and the width of the 90-vertex comparison graph."""

from collections import Counter, deque
from itertools import combinations, permutations

from gadget_csp import decode, oriented_pieces
from mixed_gadget_graph import PORTS, gadget
from recursive_gadgets import expand

# Each row introduces a new vertex on boundary 0,1,2. Its mask selects
# edges to these vertices. The three (piece, permutation) pairs identify the
# pieces placed on the faces 013, 023, 123. Piece 0 is three isolated vertices.
RECIPE = [
    (7, (0, 0), (0, 0), (0, 0)),
    (3, (0, 0), (0, 0), (1, 0)),
    (0, (0, 0), (2, 2), (2, 1)),
    (1, (0, 0), (0, 0), (3, 3)),
    (0, (0, 0), (3, 5), (4, 4)),
    (1, (0, 0), (0, 0), (3, 0)),
    (0, (0, 0), (6, 1), (4, 4)),
    (1, (0, 0), (0, 0), (7, 0)),
    (1, (0, 0), (0, 0), (7, 1)),
    (1, (0, 0), (0, 0), (8, 0)),
    (3, (0, 0), (0, 0), (0, 0)),
    (2, (0, 0), (11, 1), (1, 0)),
    (0, (0, 0), (2, 2), (12, 1)),
    (0, (0, 0), (3, 4), (13, 5)),
    (0, (0, 0), (0, 0), (14, 0)),
    (0, (0, 0), (15, 2), (7, 1)),
    (0, (0, 0), (8, 0), (16, 4)),
    (0, (0, 0), (0, 0), (17, 0)),
    (0, (0, 0), (10, 1), (18, 2)),
    (0, (0, 0), (9, 0), (19, 0)),
    (0, (0, 0), (8, 0), (20, 1)),
    (0, (0, 0), (5, 4), (21, 4)),
]


def construct_piece():
    pieces = [[set(), set(), set()]]
    orders = list(permutations(range(3)))
    faces = ((0, 1, 3), (0, 2, 3), (1, 2, 3))
    for mask, *children in RECIPE:
        graph = [set() for _ in range(4)]
        for i in range(3):
            if mask & (1 << i):
                graph[i].add(3)
                graph[3].add(i)
        for (child, order), face in zip(children, faces, strict=True):
            source = pieces[child]
            mapping = [face[orders[order].index(i)] for i in range(3)]
            mapping += list(range(len(graph), len(graph) + len(source) - 3))
            graph.extend(set() for _ in source[3:])
            for i, neighbors in enumerate(source):
                graph[mapping[i]].update(mapping[j] for j in neighbors)
        pieces.append(graph)
    return pieces[-1]


def eliminate(graph, v):
    neighbors = graph[v]
    for u in neighbors:
        graph[u].discard(v)
        graph[u].update(neighbors - {u})
    del graph[v]


def width_order(graph, bound):
    remaining = {i: set(row) for i, row in enumerate(graph)}
    order = []
    while remaining:
        eligible = [v for v, row in remaining.items() if len(row) <= bound]
        if not eligible:
            raise ValueError("no eligible vertex for the supplied width heuristic")

        def score(v):
            neighbors = remaining[v]
            fill = sum(j not in remaining[i] for i, j in combinations(neighbors, 2))
            return fill, len(neighbors), v

        v = min(eligible, key=score)
        order.append(v)
        eliminate(remaining, v)
    return order


def verify_order(graph, order, bound):
    remaining = {i: set(row) for i, row in enumerate(graph)}
    if sorted(order) != list(range(len(graph))):
        raise ValueError("elimination order is not a permutation")
    for v in order:
        if len(remaining[v]) > bound:
            raise ValueError("treewidth certificate failed")
        eliminate(remaining, v)


def distance(graph, x, y):
    depth = {x: 0}
    stack = deque([x])
    while stack:
        v = stack.popleft()
        if v == y:
            return depth[v]
        for w in graph[v] - depth.keys():
            depth[w] = depth[v] + 1
            stack.append(w)
    raise ValueError("terminals are disconnected")


def small_dyadic_cycle(graph):
    rows = [sum(1 << w for w in neighbors) for neighbors in graph]

    def search(start, v, used, length):
        if length in (3, 7, 15) and rows[v] & (1 << start):
            return True
        if length == 15:
            return False
        options = rows[v] & ~used
        while options:
            bit = options & -options
            options ^= bit
            if search(start, bit.bit_length() - 1, used | bit, length + 1):
                return True
        return False

    return any(search(s, s, (2 << s) - 1, 0) for s in range(len(graph)))


def verify_cycle(graph, cycle):
    if len(set(cycle)) != len(cycle):
        raise ValueError("cycle repeats a vertex")
    for a, b in zip(cycle, cycle[1:] + cycle[:1], strict=True):
        if b not in graph[a]:
            raise ValueError("cycle uses a nonexistent edge")


def check_width_four():
    graph = construct_piece()
    if len(graph) != 105 or Counter(map(len, graph)) != {2: 2, 3: 102, 4: 1}:
        raise ValueError("unexpected piece")
    for v, row in enumerate(graph):
        if v in row or any(v not in graph[w] for w in row):
            raise ValueError("piece is not a simple undirected graph")
    x, y = [v for v, row in enumerate(graph) if len(row) == 2]
    if distance(graph, x, y) != 16:
        raise ValueError("unexpected terminal distance")
    order = width_order(graph, 3)
    verify_order(graph, order, 3)

    graph[x].add(y)
    graph[y].add(x)
    verify_order(graph, [v for v in order if v != x] + [x], 4)
    if min(map(len, graph)) != 3 or small_dyadic_cycle(graph):
        raise ValueError("width-four example failed")
    cycle = [
        0,
        8,
        9,
        2,
        17,
        25,
        27,
        16,
        30,
        26,
        29,
        18,
        21,
        19,
        1,
        34,
        36,
        33,
        37,
        35,
        38,
        31,
        40,
        42,
        32,
        3,
        15,
        14,
        11,
        13,
        12,
        10,
    ]
    verify_cycle(graph, cycle)
    print("105 vertices, minimum degree 3, width at most 4, shortest dyadic cycle 32")


def triangular_expansion(base):
    triangle = ([[1, 2], [0, 2], [0, 1]], (0, 1, 2))
    return expand(base, [triangle] * len(base))


def width_at_most(graph, bound):
    """Decide by enumerating reachable sets of already eliminated vertices.

    Remaining vertices v,w are adjacent after fill exactly when a v-w path
    in the original graph has all its internal vertices in the removed set.
    This characterizes the fill independently of the prefix order.
    """
    n = len(graph)
    rows = [sum(1 << w for w in row) for row in graph]
    full = (1 << n) - 1
    reachable = bytearray(1 << n)
    reachable[0] = 1
    for removed, reached in enumerate(reachable):
        if not reached:
            continue
        outside = full ^ removed
        for v in range(n):
            bit = 1 << v
            if not (outside & bit) or reachable[removed | bit]:
                continue
            connected = rows[v]
            fringe = connected & removed
            while fringe:
                next_bit = fringe & -fringe
                fringe ^= next_bit
                neighbors = rows[next_bit.bit_length() - 1]
                fringe |= neighbors & removed & ~connected
                connected |= neighbors
            if (connected & outside & ~bit).bit_count() <= bound:
                reachable[removed | bit] = 1
    return bool(reachable[-1])


def check_ninety():
    base = decode(b"EFz_")  # K3,3
    library = list(oriented_pieces().values())
    graph = expand(base, [library[i] for i in (6, 7, 8, 7, 8, 6)])
    verify_order(graph, width_order(graph, 5), 5)
    # Each copy contracts to a triangle rooted at the three ports.
    cycle = [0, 5, 1, 8, 12, 7, 13, 9, 14, 2, 6]
    verify_cycle(gadget(15), cycle)
    if not set(PORTS[15]) <= set(cycle):
        raise ValueError("minor cycle misses a port")
    if width_at_most(triangular_expansion(base), 4):
        raise ValueError("the triangular expansion has width at most four")
    print("90-vertex K3,3 gadget example has treewidth exactly 5")


if __name__ == "__main__":
    check_width_four()
    check_ninety()
