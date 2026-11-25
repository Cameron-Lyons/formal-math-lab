"""Find groups of single-2 caps with the same 25 T patterns above a given pivot."""

import argparse
from collections import defaultdict


def cap_groups(pivot):
    """Map each pattern-set bitmask to all compatible caps containing exactly one 2."""
    if len(pivot) != 11 or set(pivot) - set("012"):
        raise ValueError("the pivot must contain exactly 11 ternary digits")
    cells = [0] * 25 + [int(digit) for digit in pivot]
    # A row r starts at r². Filling from the pivot upward fixes all three
    # lower cells of each T before its top cell is chosen.
    placements = [
        (r * r + column, (r + 1) ** 2 + column)
        for r in range(4, -1, -1)
        for column in range(2 * r + 1)
    ]
    groups = defaultdict(list)

    def visit(index, used, has_two):
        if index == len(placements):
            if has_two:
                groups[used].append("".join(map(str, cells[:25])))
            return
        top, left = placements[index]
        triple = 9 * cells[left] + 3 * cells[left + 1] + cells[left + 2]
        for color in range(2 if has_two else 3):
            bit = 1 << (27 * color + triple)
            if used & bit:
                continue
            cells[top] = color
            visit(index + 1, used | bit, has_two or color == 2)

    visit(0, 0, False)
    return groups


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pivot", help="eleven ternary digits")
    parser.add_argument(
        "--min-caps", type=int, default=15, help="minimum group size (default 15)"
    )
    args = parser.parse_args()
    if args.min_caps < 1:
        parser.error("--min-caps must be positive")
    try:
        groups = cap_groups(args.pivot)
    except ValueError as error:
        parser.error(str(error))
    # Each output line gives the cap count and a six-row prefix for splice_search.
    matches = [
        (len(caps), min(caps) + args.pivot)
        for caps in groups.values()
        if len(caps) >= args.min_caps
    ]
    for count, prefix in sorted(matches, key=lambda match: (-match[0], match[1])):
        print(count, prefix)


if __name__ == "__main__":
    main()
