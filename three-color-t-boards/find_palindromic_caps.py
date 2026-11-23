"""Find interchangeable mirror-symmetric caps above an eleven-cell palindromic pivot."""
import argparse
from collections import Counter, defaultdict
from itertools import product

from verify_splice import canonical_palindromic_prefix


def cap_groups(pivot):
    """Group canonical five-row caps by their 25 upper patterns, including the pivot."""
    if len(pivot) != 11 or set(pivot) - set("012") or pivot != pivot[::-1]:
        raise ValueError("the pivot must be an eleven-digit ternary palindrome")
    groups = defaultdict(list)
    rows = [pivot]

    def build_above(mask):
        lower = rows[-1]
        if len(lower) == 1:
            prefix = rows[::-1]
            if canonical_palindromic_prefix(prefix):
                groups[mask].append("".join(prefix[:-1]))
            return

        width = len(lower) - 2
        half = width // 2
        triples = [int(lower[j:j+3], 3) for j in range(width)]
        # Two mirrored placements have the same top color. Equal lower
        # triples there would repeat a pattern whichever top color is chosen.
        if any(triples[j] == triples[-1-j] for j in range(half)):
            return
        row = ["0"] * width

        def place(j, used):
            if j > half:
                rows.append("".join(row))
                build_above(used)
                rows.pop()
                return
            for color in range(1 if width == 1 else 3):
                shift = 27 * color
                bits = (1 << (shift + triples[j])) | (1 << (shift + triples[-1-j]))
                if not bits & used:
                    row[j] = row[-1-j] = str(color)
                    place(j + 1, used | bits)

        place(0, mask)

    build_above(0)
    return groups


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pivot", nargs="?")
    parser.add_argument("--census", action="store_true",
                        help="count canonical caps by group size over all 729 palindromic pivots")
    parser.add_argument("--min-caps", type=int, default=2)
    args = parser.parse_args()
    if args.census == bool(args.pivot):
        parser.error("supply either a pivot or --census")
    if args.min_caps < 1:
        parser.error("--min-caps must be positive")
    if args.census:
        histogram = Counter()
        for digits in product("012", repeat=6):
            half = "".join(digits)
            groups = cap_groups(half + half[-2::-1])
            histogram.update(map(len, groups.values()))
        print("Caps per group | Number of groups")
        for size, count in sorted(histogram.items()):
            print(f"{size:>14} | {count:,}")
        total = sum(size * count for size, count in histogram.items())
        print(f"{total:,} canonical cap–pivot prefixes")
    else:
        try:
            groups = cap_groups(args.pivot)
        except ValueError as error:
            parser.error(str(error))
        for count, prefix in sorted((len(caps), min(caps) + args.pivot)
                                    for caps in groups.values() if len(caps) >= args.min_caps):
            print(count, prefix)
