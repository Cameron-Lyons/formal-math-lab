"""Construct a longest snake in a 15-row grid and check its geometry.

Run without arguments to verify every family. With a width argument, print
the column masks from left to right, with bit zero representing the top row.
"""

import sys

PERIOD = 6
GAIN = 56
# Keep each witness in column order, grouped by board width.
# fmt: off
EXCEPTIONS = {
    1: 15, 2: 23, 3: 32, 4: 41, 5: 49, 8: 77, 11: 105, 13: 123,
    15: 142, 19: 179, 25: 235,
}

BLOCK = (3511, 7021, 14041, 28081, 23407, 30424)

LEFT_10 = (
    30590, 23875, 25437, 9943, 28080, 23399, 14045, 28081, 23407, 30424,
)
RIGHT_8 = (3511, 7021, 14041, 28087, 23396, 22215, 21945, 30575)
LEFT_12 = (
    30495, 21937, 22255, 23320, 28087, 9389, 28075, 23402, 14043, 28081,
    23407, 30424,
)
RIGHT_19 = (
    3511, 7021, 14043, 28082, 23395, 30429, 3509, 7021, 14027, 28090,
    23395, 30429, 3509, 31597, 18123, 15802, 24931, 23901, 30583,
)
RIGHT_10 = (
    3511, 31597, 18139, 23990, 29549, 1755, 30130, 23907, 24925, 16247,
)
LEFT_19 = (
    30583, 23901, 25411, 11998, 27057, 23407, 22232, 23991, 25453, 11995,
    27062, 23404, 22232, 23991, 25453, 9947, 28086, 23404, 30424,
)
LEFT_8 = (31607, 20181, 29109, 4973, 30427, 19894, 23404, 30424)

# Choose the two ends by the width modulo six.
CAPS = (
    (LEFT_10, RIGHT_8),
    (LEFT_12, RIGHT_19),
    (LEFT_10, RIGHT_10),
    (LEFT_19, RIGHT_8),
    (LEFT_8, RIGHT_8),
    (LEFT_19, RIGHT_10),
)

SHORT = {
    1: (32767,),
    2: (24029, 30583),
    3: (30719, 22529, 28671),
    4: (32247, 18205, 14563, 28606),
    5: (28535, 22997, 22045, 21955, 30590),
    6: (30711, 23581, 25571, 13886, 21953, 30591),
    7: (32190, 18147, 31517, 3509, 30381, 23211, 28398),
    8: (30583, 21845, 13654, 27995, 23405, 22069, 21973, 30583),
    9: (30583, 21917, 22243, 23346, 27099, 11885, 25525, 23765, 30583),
    10: (
        16095, 25457, 23951, 22232, 23415, 28045, 9947, 25430, 23893, 30583,
    ),
    11: (
        30583, 21853, 22883, 28090, 14027, 23405, 28085, 9941, 25437, 23875,
        30590,
    ),
    12: (
        30575, 21945, 22215, 23396, 28087, 14041, 23407, 28080, 9943, 25437,
        23875, 30590,
    ),
    13: (
        30575, 21945, 22215, 23396, 28087, 14041, 23405, 28087, 9944, 25455,
        23969, 21679, 30648,
    ),
    14: (
        32247, 18205, 30947, 3762, 29403, 23405, 28086, 14043, 23405, 28085,
        9941, 25437, 23875, 30590,
    ),
    15: (
        32375, 17245, 32099, 1466, 30411, 23405, 28086, 14043, 23405, 28087,
        9944, 25455, 23969, 21679, 30648,
    ),
    17: (
        30583, 23901, 24931, 15802, 18123, 31597, 3509, 30429, 23395, 28090,
        14027, 23405, 28085, 9941, 25437, 23875, 30590,
    ),
    19: (
        30575, 21945, 22215, 23396, 28087, 14041, 7021, 3511, 30424, 23407,
        28081, 14041, 23405, 28087, 9944, 25455, 23969, 21679, 30648,
    ),
    21: (
        30439, 23221, 27357, 11107, 28090, 18123, 31597, 3510, 30427, 23405,
        27061, 11997, 25443, 23994, 22219, 23405, 28085, 9941, 25437, 23875,
        30590,
    ),
    23: (
        30583, 23901, 16739, 23994, 22219, 23405, 28086, 9947, 25453, 23991,
        22232, 23407, 28081, 9947, 25452, 23991, 22233, 23407, 28080, 9943,
        25437, 23875, 30590,
    ),
    25: (
        30575, 21945, 22215, 23396, 28087, 14041, 7021, 3511, 30424, 23407,
        28081, 14041, 7021, 3511, 30424, 23407, 28081, 14041, 23405, 28087,
        9944, 25455, 23969, 21679, 30648,
    ),
}
# fmt: on


def snake(n: int) -> tuple[int, ...]:
    """Return column masks of an optimal induced path at width n."""
    if n < 1:
        raise ValueError("width must be positive")
    if n in SHORT:
        return SHORT[n]
    left, right = CAPS[n % PERIOD]
    copies = (n - len(left) - len(right)) // PERIOD
    if copies < 0:
        raise ValueError("missing short witness")
    return left + BLOCK * copies + right


def signature(columns: tuple[int, ...]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Check the induced graph is a path forest and describe its right boundary."""
    if not columns or any(not 0 < mask < 2**15 for mask in columns):
        raise ValueError("expected nonempty columns of height 15")
    last = len(columns) - 1
    cells = {(x, y) for x, col in enumerate(columns) for y in range(15) if col >> y & 1}
    graph = {
        (x, y): cells.intersection(((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)))
        for x, y in cells
    }
    if any(len(neighbors) > 2 for neighbors in graph.values()):
        raise ValueError("branch in the induced graph")
    degrees = tuple(
        len(graph[last, y]) if (last, y) in cells else -1 for y in range(15)
    )
    unseen = set(cells)
    components = []
    while unseen:
        stack = [unseen.pop()]
        vertices = degree_sum = boundary = 0
        while stack:
            x, y = stack.pop()
            vertices += 1
            neighbors = graph[x, y]
            degree_sum += len(neighbors)
            if x == last:
                boundary |= 1 << y
            for cell in neighbors:
                if cell in unseen:
                    unseen.remove(cell)
                    stack.append(cell)
        if degree_sum != 2 * (vertices - 1):
            raise ValueError("cycle in the induced graph")
        components.append(boundary)
    return degrees, tuple(sorted(components))


def verify() -> None:
    if len(BLOCK) != PERIOD or sum(mask.bit_count() for mask in BLOCK) != GAIN:
        raise ValueError("incorrect block width or gain")
    for residue, (left, right) in enumerate(CAPS):
        base = len(left) + len(right)
        if base % PERIOD != residue:
            raise ValueError("cap widths do not match their residue")
        boundary = signature(left)
        if 0 in boundary[1] or signature(left + BLOCK) != boundary:
            raise ValueError("the block does not restore the boundary")
        if sum(m.bit_count() for m in left + right) != (28 * base + 10) // 3:
            raise ValueError("incorrect base snake size")
        if signature(left + right)[1] != ((left + right)[-1],):
            raise ValueError("disconnected base snake")
    last = max(len(left) + len(right) for left, right in CAPS)
    for n in range(1, max(last, *EXCEPTIONS, *SHORT) + 1):
        columns = snake(n)
        expected = EXCEPTIONS.get(n, (28 * n + 10) // 3)
        if len(columns) != n or sum(mask.bit_count() for mask in columns) != expected:
            raise ValueError(f"incorrect size at width {n}")
        if signature(columns)[1] != (columns[-1],):
            raise ValueError(f"disconnected snake at width {n}")


if __name__ == "__main__":
    verify()
    if len(sys.argv) == 1:
        print(f"Verified all short snakes and all {PERIOD} repeatable families.")
    else:
        print(*snake(int(sys.argv[1])))
