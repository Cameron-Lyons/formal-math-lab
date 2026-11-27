"""Check the finite rank calculation for nonstarred families on fifteen points."""

from itertools import combinations, pairwise

POINTS = 15
FULL = (1 << POINTS) - 1


def is_progression(mask: int) -> bool:
    points = [i for i in range(POINTS) if mask & (1 << i)]
    if len(points) <= 2:
        return bool(points)
    return all(b - a == points[1] - points[0] for a, b in pairwise(points))


def binary_dependencies(rows: list[int]) -> list[int]:
    """Enumerate all nonempty subsets of the input rows whose XOR is zero."""
    pivots: dict[int, tuple[int, int]] = {}
    kernel: list[int] = [0]
    for index, row in enumerate(rows):
        support = 1 << index
        while row:
            leading = row.bit_length() - 1
            if leading not in pivots:
                pivots[leading] = (row, support)
                break
            pivot, sources = pivots[leading]
            row ^= pivot
            support ^= sources
        if not row:
            # This relation uses the new index, so it doubles the kernel.
            kernel += [previous ^ support for previous in kernel]
    return kernel[1:]


def main() -> None:
    aps = {p for p in range(1, FULL + 1) if is_progression(p)}
    short = sorted(p for p in aps if 2 <= p.bit_count() <= 6)
    coordinates = [0, *sorted(p for p in aps if p.bit_count() in (1, 2, 3, 4, 6))]
    rows = [sum(1 << j for j, t in enumerate(coordinates) if p & t == t) for p in short]
    relations = binary_dependencies(rows)
    compatible = 0
    for indices in relations:
        support = [p for i, p in enumerate(short) if indices & (1 << i)]
        if any(a & b not in aps for a, b in combinations(support, 2)):
            continue
        compatible += 1
        common = FULL
        for candidate in range(1, FULL + 1):
            if all(candidate & p in aps for p in support):
                common &= candidate
        if not common:
            raise ValueError(f"Support with no forced common point: {support}")

    if (len(short), len(coordinates), len(relations), compatible) != (
        220,
        215,
        1023,
        13,
    ):
        raise ValueError("Unexpected finite rank counts")
    print(
        f"{len(short)} rows, {len(coordinates)} columns, {len(relations)} nonzero binary relations."
    )
    print(f"All {compatible} pairwise compatible supports force a common point.")


if __name__ == "__main__":
    main()
