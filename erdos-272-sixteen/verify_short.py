"""Rank-score and marked-clique check for intersections of length at most six."""

import argparse
import io
import subprocess
import sys
from collections import Counter
from itertools import combinations

from verify_near import LIMIT, POINTS, progressions, verify_star_bound


def classify(ap):
    short = {p for p in ap if p.bit_count() <= 6}
    terms = [p for p in short if p.bit_count() in (3, 4, 6)]

    def score(a):
        size = a.bit_count()
        return 1 + size * (size - 1) // 2 - size - sum((a & p) == p for p in terms)

    if any(score(p) != 0 for p in short):
        raise ValueError("A short progression has nonzero score")
    marked = [a for a in range(1, LIMIT) if a not in short and score(a) <= 0]
    return short, marked


def verify_short_relations(short):
    """Every binary dependence possible in an intersecting family forces a common point."""
    # A singleton member would already force a common point.
    rows = sorted(p for p in short if p.bit_count() >= 2)
    coordinates = [0, *sorted(p for p in short if p.bit_count() != 5)]
    vectors = [
        sum(1 << i for i, t in enumerate(coordinates) if p & t == t) for p in rows
    ]
    points = [1 << i for i in range(POINTS)]
    pairs = [p for p in rows if p.bit_count() == 2]
    # Intersecting pairs lie in a star or in a triangle.
    pools = [{p for p in pairs if p & x} for x in points]
    pools.extend({a | b, a | c, b | c} for a, b, c in combinations(points, 3))
    relations = set()
    for pool in pools:
        pivots = {}
        kernel = [0]
        for j, (p, vector) in enumerate(zip(rows, vectors, strict=True)):
            if p.bit_count() == 2 and p not in pool:
                continue
            support = 1 << j
            while vector:
                leading = vector.bit_length()
                if leading not in pivots:
                    pivots[leading] = (vector, support)
                    break
                other, used = pivots[leading]
                vector ^= other
                support ^= used
            else:
                # A zero row gives a new independent relation.
                kernel += [r ^ support for r in kernel]
        relations.update(kernel[1:])

    # These four members force the middle point of a five-term progression.
    index = {p: j for j, p in enumerate(rows)}
    patterns = []
    for p in rows:
        if p.bit_count() == 5:
            a, b, x, c, e = [bit for bit in points if p & bit]
            patterns.append(sum(1 << index[s] for s in (p, a | x, x | e, b | x | c)))
    for relation in relations:
        if not any((relation & pattern) == pattern for pattern in patterns):
            raise ValueError("A relation omits every common-point pattern")
    if len(relations) != 16:
        raise ValueError(f"Unexpected number of binary relations: {len(relations)}")


def marked_collections(short, marked):
    # Each recursion adds the least-indexed remaining vertex, so each
    # compatible collection is counted exactly once.
    later_neighbors = []
    for i, a in enumerate(marked):
        later_neighbors.append(
            sum(1 << j for j in range(i + 1, len(marked)) if (a & marked[j]) in short)
        )

    def visit(candidates, chosen):
        yield chosen
        while candidates:
            bit = candidates & -candidates
            candidates ^= bit
            j = bit.bit_length() - 1
            yield from visit(candidates & later_neighbors[j], (*chosen, marked[j]))

    yield from visit((1 << len(marked)) - 1, ())


def reflected(mask):
    return sum(1 << (POINTS - 1 - j) for j in range(POINTS) if mask & (1 << j))


def print_instances(target, short, marked):
    """Emit the exact set of marks of each possible target family."""
    print(target, len(marked))
    print(*marked)
    reflection = {a: reflected(a) for a in marked}
    if set(reflection.values()) != set(marked):
        raise ValueError("The marked set is not reflection invariant")
    count = 0
    for chosen in marked_collections(short, marked):
        if len(chosen) < target - 121:
            continue
        if chosen <= tuple(sorted(reflection[a] for a in chosen)):
            print(len(chosen), *chosen)
            count += 1
    print(0, count)


def print_quartets(short, marked, first, end, output=sys.stdout):
    """Emit canonical choices for the four earliest marks of a 125-family."""

    def mark_order(a):
        short_subsets = sum((a & p) == p for p in short)
        return short_subsets << (POINTS - a.bit_count()), a

    ordered = sorted(marked, key=mark_order)
    sevens = {p for p in progressions() if p.bit_count() == 7}
    if len(sevens) != 14 or set(ordered[-14:]) != sevens:
        raise ValueError("The last fourteen marks must be the seven-term progressions")
    position = {a: i for i, a in enumerate(ordered)}
    image = [position[reflected(a)] for a in ordered]
    print(len(ordered), file=output)
    print(*ordered, file=output)
    count = 0
    for seeds in marked_collections(short, ordered):
        if len(seeds) != 4 or not first <= position[seeds[0]] < end:
            continue
        indices = tuple(position[a] for a in seeds)
        if indices <= tuple(sorted(image[j] for j in indices)):
            print(4, *seeds, file=output)
            count += 1
    if first == 0 and end == len(ordered) and count != 6129:
        raise ValueError(f"Unexpected number of canonical quartets: {count}")
    print(0, count, file=output)
    return count


def replay(short, marked, first, end, checker, cost=None):
    """Require a completed exclusion for every canonical quartet."""
    instances = io.StringIO()
    expected = print_quartets(short, marked, first, end, instances)
    requested = {
        tuple(map(int, line.split()[1:]))
        for line in instances.getvalue().splitlines()[2:-1]
    }
    if len(requested) != expected:
        raise ValueError("Duplicate quartet in the enumeration")
    if cost is None:
        result = subprocess.run(
            [checker, "quartets"],
            input=instances.getvalue(),
            text=True,
            stdout=subprocess.PIPE,
            check=True,
        )
        summary = f"Excluded 125 members in {expected} quartets by private triples."
        if result.stdout.strip() != summary:
            raise ValueError(f"Incomplete private-triple check: {result.stdout}")
        print(summary)
        return

    # Alternative replay using graph search and then the individual cost cases.
    lines = subprocess.run(
        [checker, "--defer-seven"],
        input=instances.getvalue(),
        text=True,
        stdout=subprocess.PIPE,
        check=True,
    ).stdout.splitlines()
    summary = lines.pop().split()
    if len(summary) != 4 or summary[::2] != ["checked", "deferred"]:
        raise ValueError(f"Unexpected graph summary {summary}")
    direct, deferred = int(summary[1]), int(summary[3])
    if direct + deferred != expected or len(lines) != deferred:
        raise ValueError("Incomplete graph check")
    catalog = subprocess.run(
        [cost, "short", "list"], text=True, stdout=subprocess.PIPE, check=True
    ).stdout.splitlines()
    ids = {}
    for line in catalog:
        case_id, *roots = map(int, line.split())
        ids[tuple(roots)] = case_id
    if len(ids) != 248 or len(set(ids.values())) != 248:
        raise ValueError("Incomplete private-triple case catalog")
    for line in lines:
        fields = line.split()
        roots = tuple(map(int, fields[1:]))
        if fields[0] != "cost" or roots not in requested or roots not in ids:
            raise ValueError(f"Unexpected deferred quartet {line}")
        requested.remove(roots)
        case_id = str(ids[roots])
        result = subprocess.run(
            [cost, "short", "0", case_id], text=True, stdout=subprocess.PIPE, check=True
        ).stdout.strip()
        if result.split()[:2] != [case_id, "closed"]:
            raise ValueError(f"Private-triple proof failed for {roots}: {result}")
        print(result, flush=True)
    print(
        f"Excluded a 125-member family in all {expected} quartets "
        f"({direct} by clique search, {deferred} by private triples)."
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--instances",
        type=int,
        choices=range(125, 131),
        help="emit exact marked subfamilies for the given family size",
    )
    mode.add_argument(
        "--quartets",
        nargs="*",
        type=int,
        metavar="INDEX",
        help="emit the four earliest marks; optionally restrict to [START, END)",
    )
    mode.add_argument(
        "--replay",
        nargs="+",
        metavar="CHECKER",
        help="use the private-triple checker, or supply GRAPH COST for the alternative replay",
    )
    parser.add_argument(
        "--range",
        nargs=2,
        type=int,
        metavar=("START", "END"),
        help="for --replay, restrict the first mark to these half-open indices",
    )
    args = parser.parse_args()
    ap = progressions()
    short, marked = classify(ap)
    if args.range is not None and args.replay is None:
        parser.error("--range applies to --replay")
    if args.instances is not None:
        print_instances(args.instances, short, marked)
        raise SystemExit
    if args.quartets is not None:
        bounds = args.quartets or [0, len(marked)]
        if len(bounds) != 2 or not 0 <= bounds[0] < bounds[1] <= len(marked):
            parser.error(
                "Supply either no indices or a half-open range within [0, 101)."
            )
        print_quartets(short, marked, *bounds)
        raise SystemExit

    for x in range(POINTS // 2):
        verify_star_bound(x)
    verify_short_relations(short)
    if args.replay is not None:
        first, end = args.range or [0, len(marked)]
        if len(args.replay) not in (1, 2):
            parser.error("Supply the private-triple checker, or both GRAPH and COST.")
        if not 0 <= first < end <= len(marked):
            parser.error("The half-open range must lie within [0, 101).")
        replay(short, marked, first, end, *args.replay)
        raise SystemExit
    counts = Counter(map(len, marked_collections(short, marked)))
    print(
        f"{len(marked)} marked subsets, of which {sum(a in ap for a in marked)} are progressions"
    )
    for size in range(4, max(counts) + 1):
        print(f"{size} marked members: {counts[size]} compatible collections")
    if len(marked) != 101 or max(counts) != 9:
        raise ValueError("Unexpected marked count or clique number")
    print(
        f"The rank and marked-set counts alone give {121 + max(counts)}. "
        "Use --replay for the exact bound of 124."
    )
