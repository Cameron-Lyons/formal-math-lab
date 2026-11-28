"""Construct longest snakes on 13-by-n boards, with one integer per column.

Bit r of a mask selects row r, counting from zero. Run with no arguments to
verify the six infinite families and all short boards. Supply n to print the
column masks of an optimal snake. Only the Python standard library is needed.
"""

import sys
from collections import deque

# Each left cap ends at the same frontier. The six-column block returns to it.
LEFT_11 = (8119, 4317, 8035, 442, 7883, 4973, 4535, 7896, 879, 7601, 5853)
LEFT_12 = (8055, 4501, 7901, 867, 7610, 5835, 4973, 4535, 7896, 879, 7601, 5853)
BLOCK = (4965, 4535, 7896, 879, 7601, 5853)
RIGHT_4 = (7013, 3509, 5333, 7287)
RIGHT_5 = (7015, 2488, 6351, 6001, 7583)
RIGHT_6 = (7013, 3511, 1240, 7279, 5041, 7903)
RIGHT_8 = (7015, 3512, 5839, 7025, 2461, 6373, 5925, 7655)

# The outer index is the width modulo six.
CAPS = (
    (LEFT_12, RIGHT_6),
    (LEFT_11, RIGHT_8),
    (LEFT_12, RIGHT_8),
    (LEFT_11, RIGHT_4),
    (LEFT_11, RIGHT_5),
    (LEFT_12, RIGHT_5),
)

SHORT = (
    (),
    (8191,),
    (7645, 6007),
    (8187, 4109, 8183),
    (7671, 5909, 4333, 8123),
    (7671, 5397, 5557, 5805, 7099),
    (8063, 4545, 7742, 995, 7197, 6135),
    (7671, 4889, 5871, 5552, 5919, 6369, 4031),
    (8055, 4565, 7702, 987, 7277, 6069, 4309, 8055),
    (8055, 4509, 7907, 826, 7627, 5741, 5045, 4309, 8055),
    (8119, 4317, 5987, 5554, 5851, 6765, 2997, 6365, 5987, 7614),
    (8119, 4317, 8035, 442, 7883, 4973, 7607, 1240, 7279, 5041, 7903),
    (8055, 4501, 7901, 867, 7610, 5835, 4973, 7607, 1240, 7279, 5041, 7903),
    (7647, 5969, 6351, 3000, 6759, 5853, 3505, 7023, 5848, 5527, 5917, 6371, 4030),
    (7903, 5041, 7279, 1496, 7479, 4973, 5851, 5558, 7533, 459, 7738, 5091, 7197, 2039),
)


def snake(n):
    """Return n column masks of a longest snake."""
    if n < 1:
        raise ValueError("width must be positive")
    if n < len(SHORT):
        return SHORT[n]
    left, right = CAPS[n % 6]
    k = (n - len(left) - len(right)) // len(BLOCK)
    return left + BLOCK * k + right


def maximum(n):
    if n < 1:
        raise ValueError("width must be positive")
    if n <= 6:
        return (13, 20, 28, 36, 43, 51)[n - 1]
    return 8 * n + (4 if n % 6 in (0, 4, 5) else 3)


def frontier(columns):
    """Verify a union of paths. Return frontier degrees and component masks.

    A zero component mask denotes a component missing the last column.
    Matching signatures of path forests in which all components meet the cut
    allow exactly the same continuations: the degrees bound new adjacencies,
    and the component masks decide mergers and cycles.
    """
    if not columns or any(not 0 < mask < 2**13 for mask in columns):
        raise ValueError("each column must be a nonempty 13-bit mask")
    cells = {
        (x, y) for x, mask in enumerate(columns) for y in range(13) if mask & (1 << y)
    }
    neighbors = {
        (x, y): [
            cell
            for cell in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1))
            if cell in cells
        ]
        for x, y in cells
    }
    if any(len(adjacent) > 2 for adjacent in neighbors.values()):
        raise ValueError("branch in the induced graph")
    unseen = set(cells)
    last = len(columns) - 1
    component_masks = []
    while unseen:
        queue = deque([unseen.pop()])
        vertices = degree_sum = mask = 0
        while queue:
            x, y = queue.popleft()
            vertices += 1
            degree_sum += len(neighbors[x, y])
            if x == last:
                mask |= 1 << y
            for cell in neighbors[x, y]:
                if cell in unseen:
                    unseen.remove(cell)
                    queue.append(cell)
        if degree_sum != 2 * (vertices - 1):
            raise ValueError("cycle in the induced graph")
        component_masks.append(mask)
    degrees = tuple(
        len(neighbors[last, y]) if (last, y) in cells else -1 for y in range(13)
    )
    return degrees, tuple(sorted(component_masks))


def verify():
    expected = ((1, -1, 1, 2, 2, -1, 1, 2, -1, 1, 2, -1, 1), (1, 220, 5632))
    assert sum(mask.bit_count() for mask in BLOCK) == 48
    for left in (LEFT_11, LEFT_12):
        assert frontier(left) == frontier(left + BLOCK) == expected
    for r, (left, right) in enumerate(CAPS):
        base = len(left) + len(right)
        assert 15 <= base <= 20 and base % 6 == r
    for n in range(1, 21):
        columns = snake(n)
        assert len(columns) == n
        assert sum(mask.bit_count() for mask in columns) == maximum(n)
        # A single component meeting the nonempty last column certifies a connected snake.
        assert frontier(columns)[1] == (columns[-1],)


if __name__ == "__main__":
    verify()
    if len(sys.argv) == 1:
        print("Verified all 14 short snakes and all six repeatable families.")
    else:
        print(*snake(int(sys.argv[1])))
