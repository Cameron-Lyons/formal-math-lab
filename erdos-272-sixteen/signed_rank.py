"""Verify the signed progression counts used in signed-rank.md on all of [16]."""

from itertools import pairwise

N = 16
SIZE = 1 << N
# The index is the length. Index 0 is the constant term.
COEFFICIENT = (1, -1, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1)


def is_progression(mask):
    points = [x for x in range(N) if mask & (1 << x)]
    if len(points) <= 2:
        return bool(points)
    step = points[1] - points[0]
    return all(b - a == step for a, b in pairwise(points))


def check():
    progressions = {mask for mask in range(1, SIZE) if is_progression(mask)}
    score = [0] * SIZE
    score[0] = COEFFICIENT[0]
    for mask in progressions:
        score[mask] = COEFFICIENT[mask.bit_count()]

    # After processing all bits, score[S] is the sum of the original
    # entries on every subset of S, including the empty-set constant.
    for x in range(N):
        bit = 1 << x
        for start in range(bit, SIZE, 2 * bit):
            for mask in range(start, start + bit):
                score[mask] += score[mask ^ bit]

    for mask in range(1, SIZE):
        if mask in progressions:
            if score[mask] != 0:
                raise ValueError(f"progression {mask} has score {score[mask]}")
        elif score[mask] <= 0:
            raise ValueError(f"non-progression {mask} has score {score[mask]}")

    extra_lengths = {9, 10, 13}
    positive = 1 + sum(COEFFICIENT[p.bit_count()] > 0 for p in progressions)
    extra = sum(p.bit_count() in extra_lengths for p in progressions)
    others = SIZE - 1 - len(progressions)
    print(f"{len(progressions)} progressions have score 0")
    print(f"{others} other nonempty subsets have strictly positive score")
    print(f"{positive} positive coordinates and {extra} equality coordinates")


if __name__ == "__main__":
    check()
