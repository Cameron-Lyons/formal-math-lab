"""Construct optimal snakes on a 14-row grid and verify the six infinite families.

Running without arguments checks the data. Supply a width to print one mask per
column from left to right. Bit zero selects the top row.
"""

import sys

# Keep the column masks grouped by snake.
# fmt: off
LEFT_8 = (15231, 11969, 12735, 5984, 13535, 11697, 15215, 1752)
LEFT_17 = (
    15359, 11777, 12767, 5968, 13527, 11701, 15213, 1755, 15798, 9068, 11992,
    10679, 7021, 14043, 11702, 15212, 1752,
)
BLOCK = (15799, 9069, 11995, 10678, 15212, 1752)
RIGHT_7 = (15799, 9069, 16091, 434, 16227, 8413, 16311)
RIGHT_8 = (15799, 9069, 16091, 438, 15204, 11975, 12729, 8047)
RIGHT_11 = (15799, 9069, 14043, 5554, 13667, 11613, 15191, 1752, 15759, 9073, 16095)
RIGHT_12 = (
    15799, 9069, 11995, 10386, 11995, 13165, 7606, 1755, 14957, 11829, 12757,
    8055,
)
RIGHT_15 = (
    15799, 9069, 16091, 146, 16091, 9069, 15797, 1757, 15203, 11706, 14027,
    4973, 12725, 11989, 15223,
)

# Index each pair of ends by the width modulo six.
CAPS = (
    (LEFT_17, RIGHT_7), (LEFT_8, RIGHT_11), (LEFT_8, RIGHT_12),
    (LEFT_8, RIGHT_7), (LEFT_8, RIGHT_8), (LEFT_8, RIGHT_15),
)

SHORT = {
    1: (16383,),
    2: (12015, 15289),
    3: (14335, 11265, 15359),
    4: (15359, 9729, 11741, 15223),
    5: (14207, 11585, 11101, 10965, 15287),
    6: (15295, 10977, 6941, 12789, 11789, 15355),
    7: (14303, 11377, 15247, 1752, 15479, 9101, 16123),
    8: (15359, 9729, 11773, 15111, 1784, 15759, 9073, 16095),
    9: (15223, 11989, 12725, 5997, 13531, 11698, 11107, 10973, 15287),
    10: (15295, 10977, 11037, 11701, 14061, 6939, 11702, 13997, 6827, 3822),
    11: (15359, 11777, 12797, 5894, 13563, 11661, 15223, 1752, 15759, 9073, 16095),
    12: (
        15295, 11937, 12719, 5992, 13528, 11703, 7021, 14043, 11698, 11107, 10973,
        15287,
    ),
    13: (
        15359, 11777, 12767, 5968, 13527, 11701, 7021, 14043, 11702, 11108, 11975,
        12729, 8047,
    ),
    14: (
        15359, 11777, 12767, 5968, 13527, 11701, 15213, 1755, 15798, 9068, 7896,
        12471, 11949, 15291,
    ),
    17: (
        14207, 11585, 15199, 1744, 15799, 9069, 16091, 438, 15212, 11992, 12727,
        5997, 13531, 11698, 11107, 10973, 15287,
    ),
    18: (
        15359, 11777, 12767, 5968, 13527, 11701, 15213, 1755, 15798, 9068, 11992,
        10679, 7021, 14043, 11698, 11107, 10973, 15287,
    ),
}
# fmt: on


def snake(n: int) -> tuple[int, ...]:
    """Return the column masks of one longest snake."""
    if n < 1:
        raise ValueError("width must be positive")
    if n in SHORT:
        return SHORT[n]
    left, right = CAPS[n % 6]
    copies = (n - len(left) - len(right)) // len(BLOCK)
    return left + BLOCK * copies + right


def signature(columns: tuple[int, ...]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Check the induced graph is a path forest and describe its right boundary."""
    if not columns or any(not 0 < mask < 2**14 for mask in columns):
        raise ValueError("expected nonempty columns of height 14")
    last = len(columns) - 1
    cells = {(x, y) for x, col in enumerate(columns) for y in range(14) if col >> y & 1}
    graph = {
        (x, y): cells.intersection(((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)))
        for x, y in cells
    }
    if any(len(neighbors) > 2 for neighbors in graph.values()):
        raise ValueError("branch in the induced graph")
    degrees = tuple(
        len(graph[last, y]) if (last, y) in cells else -1 for y in range(14)
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
    offsets = (3, 12, 20, 30, 38, 47)
    exceptions = {1: 14, 2: 21, 5: 46, 10: 89, 11: 98, 13: 115, 14: 123, 17: 150}
    if len(BLOCK) != 6 or sum(mask.bit_count() for mask in BLOCK) != 52:
        raise ValueError("incorrect block size")
    for r, (left, right) in enumerate(CAPS):
        boundary = signature(left)
        if 0 in boundary[1] or signature(left + BLOCK) != boundary:
            raise ValueError("the block does not restore the boundary")
        base = len(left) + len(right)
        if base % 6 != r or base in exceptions or base > 24 or base in SHORT:
            raise ValueError("invalid base width")
    for n in range(1, 25):
        cols = snake(n)
        q, r = divmod(n, 6)
        expected = exceptions.get(n, 52 * q + offsets[r])
        if len(cols) != n or sum(mask.bit_count() for mask in cols) != expected:
            raise ValueError(f"incorrect size at width {n}")
        if signature(cols)[1] != (cols[-1],):
            raise ValueError(f"disconnected snake at width {n}")


if __name__ == "__main__":
    verify()
    if len(sys.argv) == 1:
        print("Verified all short snakes and all six repeatable families.")
    else:
        print(*snake(int(sys.argv[1])))
