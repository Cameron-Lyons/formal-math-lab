"""Construct a cubic graph whose first power-of-two cycle length is 128.

Use a mixture of the three-port gadgets H7 and H15 of Exoo and Garcia
(arXiv:2609.04686, section 3). Every external simple cycle uses exactly two
edges of each gadget cut it crosses, so it projects to a simple base cycle.
Conversely the internal paths on a base cycle can be chosen independently.
The program checks the gadget path intervals, all relevant base cycles, and
a 128-cycle directly in the resulting 8,628-vertex simple graph.
"""

from collections import Counter, deque
from itertools import product

# A digit 0, 1, 2 requests H15, and 3, 4, 5 requests H7. The residue
# modulo three selects the neighbor facing port u in the sorted neighbor list.
DESIGN = (
    "12000111222201120112011221012512200102411052232102110224022143210001122220130110"
    "23123002102210320110221052220141332242320122100402221121004101122310031001202233"
    "10252211113350100005220111110202011212121220033001302120204010001010102211224320"
    "02212212201152100312031222201310021001003225321012011101210122102050020120010021"
    "11010001110352020521312200030100113020521322100041012231220012101321412125212013"
    "00530022100002221200101001201052120212152212120023051021122011003041102213212020"
    "10200132211210200112422244110122020222221222051011020002113130201112512122301421"
    "001002222222104452113202512100030130211132012120220200213000"
)


def multiply(left, right):
    """Multiply determinant-one matrices modulo 31, identifying M with -M."""
    a, b, c, d = left
    e, f, g, h = right
    matrix = (
        (a * e + b * g) % 31,
        (a * f + b * h) % 31,
        (c * e + d * g) % 31,
        (c * f + d * h) % 31,
    )
    return min(matrix, tuple(-x % 31 for x in matrix))


def coset_graph():
    """620 left cosets of a subgroup of order 24 in PSL(2,31)."""
    identity = (1, 0, 0, 1)
    generators = ((0, 1, 30, 0), (2, 1, 24, 28))
    subgroup = [identity]
    seen = {identity}
    for matrix in subgroup:
        for generator in generators:
            successor = multiply(matrix, generator)
            if successor not in seen:
                seen.add(successor)
                subgroup.append(successor)
    assert len(subgroup) == 24
    # Iterate matrices of determinant one in lexicographic order. Canonical
    # representatives of the signs and then of the cosets define the numbering.
    coset = {}
    representatives = []
    for a, b, c in product(range(31), repeat=3):
        if a:
            entries = [(1 + b * c) * pow(a, -1, 31) % 31]
        elif (1 + b * c) % 31 == 0:
            entries = range(31)
        else:
            continue
        for d in entries:
            matrix = (a, b, c, d)
            if matrix != multiply(identity, matrix) or matrix in coset:
                continue
            number = len(representatives)
            representatives.append(matrix)
            for element in subgroup:
                coset[multiply(matrix, element)] = number
    assert len(coset) == 14880 and len(representatives) == 620
    bridge = (0, 12, 18, 26)
    neighbors_of_identity = {coset[multiply(h, bridge)] for h in subgroup}
    return [
        sorted(coset[multiply(g, representatives[n])] for n in neighbors_of_identity)
        for g in representatives
    ]


def distances(graph, root):
    depth = [-1] * len(graph)
    depth[root] = 0
    queue = deque([root])
    while queue:
        v = queue.popleft()
        for w in graph[v]:
            if depth[w] < 0:
                depth[w] = depth[v] + 1
                queue.append(w)
    return depth


def check_cubic(graph):
    for v, row in enumerate(graph):
        assert len(row) == len(set(row)) == 3 and v not in row
        assert all(0 <= w < len(graph) and v in graph[w] for w in row)
    assert min(distances(graph, 0)) == 0


def short_cycles(graph, limit):
    """Emit each simple cycle once, from its minimum vertex in one direction."""
    path = []
    used = set()

    def extend(root, distance, v):
        for w in graph[v]:
            if w == root and len(path) >= 3 and path[1] < v:
                yield tuple(path)
            elif w > root and w not in used and len(path) + distance[w] <= limit:
                used.add(w)
                path.append(w)
                yield from extend(root, distance, w)
                path.pop()
                used.remove(w)

    for root in range(len(graph)):
        path.append(root)
        used.add(root)
        yield from extend(root, distances(graph, root), root)
        path.pop()
        used.remove(root)


PORTS = {7: (0, 1, 2), 15: (14, 7, 0)}


def gadget(order):
    # H7 is labeled u,v,w,a,b,c,d = 0,...,6.
    h7 = [(1, 3), (3, 4), (4, 2), (5, 1), (2, 6), (3, 5), (5, 0), (0, 6), (6, 4)]
    edges = h7
    if order == 15:
        edges = h7 + [(v + 7, w + 7) for v, w in h7] + [(1, 8), (2, 14), (14, 9)]
    graph = [[] for _ in range(order)]
    for v, w in edges:
        graph[v].append(w)
        graph[w].append(v)
    return graph


def path_lengths(graph, start, end):
    """One path witness per attainable length, by exhaustive simple-path DFS."""
    paths = {}
    path = [start]

    def extend(v):
        if v == end:
            paths[len(path) - 1] = tuple(path)
            return
        for w in graph[v]:
            if w not in path:
                path.append(w)
                extend(w)
                path.pop()

    extend(start)
    return paths


def shortest_cycle_through(graph, start, end):
    """Find the shortest alternate path for an edge, then close it with the edge."""
    distance = [-1] * len(graph)
    distance[start] = 0
    queue = deque([start])
    while queue:
        v = queue.popleft()
        for w in graph[v]:
            if v == start and w == end:
                continue
            if w == end:
                return distance[v] + 2
            if distance[w] == -1:
                distance[w] = distance[v] + 1
                queue.append(w)
    raise ValueError("The edge lies on no cycle.")


def check_construction():
    """Return the adjacency lists and the verified 128-cycle in cyclic order."""
    if not __debug__:
        raise RuntimeError("Run with Python assertions enabled.")
    base = coset_graph()
    check_cubic(base)
    assert len(base) == len(DESIGN) == 620 and set(DESIGN) <= set("012345")
    sizes = [15 if int(d) < 3 else 7 for d in DESIGN]
    pieces = {size: gadget(size) for size in PORTS}
    paths = {}
    for size, piece in pieces.items():
        internal = {len(cycle) for cycle in short_cycles(piece, size)}
        expected = (
            {3, 5, 6, 7} if size == 7 else {3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15}
        )
        assert internal == expected
        for start, end in product(PORTS[size], repeat=2):
            if start == end:
                continue
            witness = path_lengths(piece, start, end)
            if size == 7:
                minimum = 2 if PORTS[size][0] in (start, end) else 3
            else:
                minimum = 3 if PORTS[size][0] in (start, end) else 5
            assert set(witness) == set(range(minimum, size))
            paths[size, start, end] = witness
    ports = []
    offsets = []
    expanded = []
    for v, row in enumerate(base):
        size = sizes[v]
        selected = row[int(DESIGN[v]) % 3]
        remaining = [w for w in row if w != selected]
        ports.append(dict(zip([selected, *remaining], PORTS[size], strict=True)))
        offset = len(expanded)
        offsets.append(offset)
        expanded.extend([offset + w for w in row] for row in pieces[size])
    connectors = []
    for v, row in enumerate(base):
        for w in row:
            start = offsets[v] + ports[v][w]
            end = offsets[w] + ports[w][v]
            expanded[start].append(end)
            if v < w:
                connectors.append((start, end))
    check_cubic(expanded)
    assert sizes.count(7) == 84 and len(expanded) == 8628
    # Independent of projection to base cycles: delete each external edge in
    # turn and find the shortest alternate path directly in the expanded graph.
    assert len(connectors) == 930
    shortest_external = min(
        shortest_cycle_through(expanded, u, v) for u, v in connectors
    )
    assert shortest_external == 65

    counts = Counter()
    witness128 = None
    # Each visited copy costs at least 3 edges including its outgoing edge.
    # Hence projected cycles of length >=22 already expand to length >64.
    for cycle in short_cycles(base, 21):
        n = len(cycle)
        counts[n] += 1
        transits = [
            paths[sizes[v], ports[v][cycle[i - 1]], ports[v][cycle[(i + 1) % n]]]
            for i, v in enumerate(cycle)
        ]
        minimum = n + sum(min(choices) for choices in transits)
        assert minimum > 64
        maximum = n + sum(max(choices) for choices in transits)
        if minimum <= 128 <= maximum and witness128 is None:
            # All transit lengths between both endpoints occur. Distribute 128-minimum
            # extra edges, then check the actual expanded cycle edge by edge.
            needed = 128 - minimum
            witness128 = []
            for v, choices in zip(cycle, transits, strict=True):
                extra = min(needed, max(choices) - min(choices))
                needed -= extra
                witness128.extend(offsets[v] + u for u in choices[min(choices) + extra])
            assert needed == 0
    assert counts == {
        15: 1984,
        16: 4185,
        17: 7440,
        18: 6200,
        19: 14880,
        20: 25668,
        21: 39680,
    }
    assert witness128 is not None and len(set(witness128)) == len(witness128) == 128
    assert all(
        witness128[(i + 1) % 128] in expanded[v] for i, v in enumerate(witness128)
    )
    return expanded, witness128


if __name__ == "__main__":
    check_construction()
    print(
        "Connected cubic base: 620 vertices; girth 15; 100037 simple cycles of length at most 21."
    )
    print(
        "Connected cubic expansion: 8628 vertices; first power-of-two cycle length 128."
    )
