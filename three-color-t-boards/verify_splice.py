"""Independently verify the splice certificate using Cartesian T placements."""
import argparse
from functools import lru_cache
from itertools import chain, pairwise, permutations, product
import json
from pathlib import Path


CERTIFICATE = Path(__file__).with_name("splice_witnesses.json")
EXTENSION = CERTIFICATE.with_name("splice_extension.json")
FURTHER = CERTIFICATE.with_name("splice_further.json")
TRANSFER = CERTIFICATE.with_name("splice_transfer.json")
NEXT = CERTIFICATE.with_name("splice_next.json")
SIXTH = CERTIFICATE.with_name("splice_sixth.json")
PAL = CERTIFICATE.with_name("splice_pal.json")
PATTERNS = set(product("012", repeat=4))
TERNARY_DIGITS = bytes.maketrans(b"012", bytes(range(3)))
ACTIONS = [(str.maketrans("012", "".join(colors)), reflect)
           for colors in permutations("012") for reflect in (False, True)]
PALETTES = [action for action in ACTIONS if not action[1]]


def split_rows(flat, start, stop):
    """Decode the rows with indices start through stop-1."""
    if len(flat) != stop * stop - start * start or set(flat) - set("012"):
        raise ValueError(f"invalid encoding for rows {start} through {stop - 1}")
    return [flat[r*r - start*start:(r+1)**2 - start*start] for r in range(start, stop)]


def reflected_rows(flat, start, stop):
    return "".join(row[::-1] for row in split_rows(flat, start, stop))


def canonical_palindromic_prefix(rows):
    """A mirrored prefix fixed row by row, with colors named in order of appearance."""
    colors = "".join(dict.fromkeys("".join(rows)))
    return colors == "012" and all(row == row[::-1] for row in rows)


@lru_cache(maxsize=64)
def cartesian_windows(start, widths):
    """Find the T placements once for each shape, using Cartesian cell coordinates."""
    cells_in_order = ((j-r, -r) for r, width in enumerate(widths, start) for j in range(width))
    positions = {cell: i for i, cell in enumerate(cells_in_order)}
    windows = []
    for x, y in positions:
        cells = ((x, y+1), (x-1, y), (x, y), (x+1, y))
        if all(cell in positions for cell in cells):
            windows.append(tuple(positions[cell] for cell in cells))
    return tuple(windows)


def patterns(rows, start):
    rows = tuple(tuple(row) for row in rows)
    widths = tuple(map(len, rows))
    flat = tuple(chain.from_iterable(rows))
    seen = set()
    for top, left, middle, right in cartesian_windows(start, widths):
        pattern = (flat[top], flat[left], flat[middle], flat[right])
        if pattern in seen:
            raise ValueError(f"repeated T {pattern}")
        seen.add(pattern)
    return frozenset(seen)


def common_set(pieces):
    iterator = iter(pieces)
    first = next(iterator)
    if any(other != first for other in iterator):
        raise ValueError("pieces disagree on their T patterns")
    return first


def combine(base, extra):
    if base["cut"] != extra["cut"]:
        raise ValueError("the two certificates use different pivot rows")
    return {"cut": base["cut"], "groups": base["groups"] + extra["groups"]}


def previous_layers(base_path=CERTIFICATE, include_next=False):
    from prepare_splice_transfer import expand_transfer
    sources = {CERTIFICATE.stem: json.loads(base_path.read_text())}
    for path in (EXTENSION, FURTHER):
        sources[path.stem] = json.loads(path.read_text())
    transfer = json.loads(TRANSFER.read_text())
    sources[TRANSFER.stem] = expand_transfer(transfer, sources)
    if include_next:
        fifth = json.loads(NEXT.read_text())
        extension_checkpoints(fifth["groups"], sources)
        sources[NEXT.stem] = fifth
    return sources


def extension_source(group, sources):
    ref = group["extends"]
    if not isinstance(ref, dict):
        raise ValueError("invalid extension source")
    layer, index = ref.get("layer"), ref.get("index")
    if (not isinstance(layer, str) or layer not in sources or type(index) is not int
            or not 0 <= index < len(sources[layer]["groups"])):
        raise ValueError("unknown extension source")
    original = sources[layer]["groups"][index]
    if (group["pivot"], group["caps"]) != (original["pivot"], original["caps"]):
        raise ValueError("extension changed its original cap or pivot")
    if not group["tails"] or min(group["tails"]) <= max(original["tails"]):
        raise ValueError("extension overlaps the original tail range")
    return original


def extension_checkpoints(groups, sources):
    """Return the exclusive DFS starting tail for each extension, in certificate order."""
    def signature(group):
        pivot = group["pivot"]
        return pivot, patterns(split_rows(group["caps"][0], 0, 5) + [pivot], 0)

    last = {}
    for layer in sources.values():
        for group in layer["groups"]:
            last[signature(group)] = max(group["tails"])
    checkpoints = {}
    for i, group in enumerate(groups):
        key = signature(group)
        if "extends" in group:
            extension_source(group, sources)
            if min(group["tails"]) <= last[key]:
                raise ValueError(f"extension at group {i} overlaps an earlier chunk")
            checkpoints[i] = last[key]
        elif key in last:
            raise ValueError(f"repeated signature without an extension source at group {i}")
        last[key] = max(group["tails"])
    return checkpoints


def uses_fifth_sources(path, groups):
    """A sixth-layer file can continue a fifth-layer group or any earlier ancestor."""
    return path.name == SIXTH.name or any(isinstance(g.get("extends"), dict)
            and g["extends"].get("layer") == NEXT.stem for g in groups)


def load_all(base_path=CERTIFICATE, include_next=True, include_sixth=None, include_pal=None):
    if include_sixth is None:
        include_sixth = include_next
    if include_pal is None:
        include_pal = include_sixth
    if include_pal and not include_sixth:
        raise ValueError("the combined palindromic certificate requires the sixth layer")
    if include_sixth and not include_next:
        raise ValueError("the sixth layer requires the fifth")
    sources = previous_layers(base_path, include_next)
    data = {"cut": sources[CERTIFICATE.stem]["cut"], "groups": []}
    for layer in sources.values():
        data = combine(data, layer)
    if include_sixth:
        extra = json.loads(SIXTH.read_text())
        extension_checkpoints(extra["groups"], sources)
        data = combine(data, extra)
    if include_pal:
        pal = json.loads(PAL.read_text())
        if not all(g.get("palindromic_upper") is True for g in pal["groups"]):
            raise ValueError("missing palindromic prefix declaration")
        data = combine(data, pal)
    return data


def verify(data, base_path=CERTIFICATE, *, include_next=None):
    cut = data["cut"]
    if not 0 < cut < 9 or not data["groups"]:
        raise ValueError("expected a nonempty certificate with an interior cut")
    groups = data["groups"]
    if include_next is not None or any("extends" in group for group in groups):
        if include_next is None:
            include_next = uses_fifth_sources(base_path, groups)
        sources = previous_layers(base_path, include_next)
        historical = [g for layer in sources.values() for g in layer["groups"]]
        # A combined certificate already contains the historical groups in order.
        pending = groups[len(historical):] if groups[:len(historical)] == historical else groups
        extension_checkpoints([g for g in pending if not g.get("palindromic_upper")], sources)
    last_tail = {}
    # A row-wise image of the full upper prefix determines its symmetry action.
    marker_actions = {}
    representatives = cap_count = tail_count = 0
    for index, group in enumerate(data["groups"]):
        pivot = group["pivot"]
        split_rows(pivot, cut, cut+1)
        caps, tails = group["caps"], group["tails"]
        for pieces in (caps, tails):
            if not pieces or any(a >= b for a, b in pairwise(pieces)):
                raise ValueError(f"group {index} requires nonempty, strictly increasing piece lists")
        markers = {tuple(split_rows(cap, 0, cut)) + (pivot,) for cap in caps}
        pal = group.get("palindromic_upper", False)
        if pal:
            if not all(canonical_palindromic_prefix(marker) for marker in markers):
                raise ValueError(f"group {index} requires canonical palindromic prefixes")
            ts = set(tails)
            for tail in tails:
                mirror = reflected_rows(tail, cut+1, 10)
                if mirror == tail or mirror not in ts:
                    raise ValueError(f"group {index} requires distinct pairs of reflected tails")
        for marker in markers:
            for action, (palette, reflected) in enumerate(ACTIONS):
                if pal and reflected:
                    continue
                image = tuple((row[::-1] if reflected else row).translate(palette) for row in marker)
                if marker_actions.setdefault(image, action) != action:
                    raise ValueError(f"ambiguous symmetry for marker {marker}")
        upper = common_set(patterns(split_rows(cap, 0, cut) + [pivot], 0)
                           for cap in caps)
        lower = common_set(patterns([pivot] + split_rows(tail, cut+1, 10), cut)
                           for tail in tails)
        if upper & lower or upper | lower != PATTERNS:
            raise ValueError(f"patterns do not partition all 81 in group {index}")
        key = (pal, pivot, upper)
        if key in last_tail:
            if "extends" not in group:
                raise ValueError(f"repeated signature without an extension source at group {index}")
            if tails[0] <= last_tail[key]:
                raise ValueError(f"overlapping tail ranges at group {index}")
        last_tail[key] = tails[-1]
        representatives += len(caps) * (len(tails) // 2 if pal else len(tails))
        cap_count += len(caps)
        tail_count += len(tails)
    return len(data["groups"]), cap_count, tail_count, representatives, 12 * representatives


def check_pivot_orbit(task):
    """Check every image in a single orbit of pivot rows, using exact board encodings."""
    pivot_key, groups, earlier = task
    windows = cartesian_windows(0, tuple(range(1, 20, 2)))
    if len(windows) != 81:
        raise ValueError("incorrect placement count")
    powers = [1 << i for i in range(81)]
    all_patterns = (1 << 81) - 1
    boards = set()
    for group in groups:
        actions = PALETTES if group.get("palindromic_upper") else ACTIONS
        for cap, tail in product(group["caps"], group["tails"]):
            rows = split_rows(cap + group["pivot"] + tail, 0, 10)
            flat = "".join(rows)
            mirror = "".join(row[::-1] for row in rows)
            for palette, reflected in actions:
                image = (mirror if reflected else flat).translate(palette)
                # Fixed width makes the base-three integer an exact board identifier.
                key = int(image, 3)
                if key in boards:
                    raise ValueError("duplicate full board")
                boards.add(key)
                digits = image.encode("ascii").translate(TERNARY_DIGITS)
                seen = 0
                for t, l, m, r in windows:
                    seen |= powers[27*digits[t] + 9*digits[l] + 3*digits[m] + digits[r]]
                if seen != all_patterns:
                    raise ValueError(f"invalid full board: {image}")
    if not earlier.issubset(boards):
        raise ValueError(f"an earlier board is absent at pivot {pivot_key}")
    return len(boards)


def pivot_orbit(row):
    return min((row[::-1] if reflected else row).translate(palette)
               for palette, reflected in ACTIONS)


def expanded_tasks(data, include_earlier=True):
    """Partition the images and the earlier witnesses by their exact pivot orbit."""
    by_pivot = {}
    for g in data["groups"]:
        by_pivot.setdefault(pivot_orbit(g["pivot"]), []).append(g)
    previous = (json.loads(CERTIFICATE.with_name("extended_family.json").read_text())
                if include_earlier else [])
    earlier = {key: set() for key in by_pivot}
    for rows in previous:
        key = pivot_orbit(rows[data["cut"]])
        if key not in earlier:
            raise ValueError(f"earlier pivot orbit {key} is missing")
        earlier[key].add(int("".join(rows), 3))
    tasks = [(key, groups, earlier[key]) for key, groups in by_pivot.items()]
    return tasks, len(previous)


def native_expanded_count(tasks, jobs, cut):
    from concurrent.futures import ThreadPoolExecutor
    import subprocess
    from tempfile import TemporaryDirectory

    with TemporaryDirectory() as work:
        binary = Path(work) / "expand_splice"
        subprocess.run(["c++", "-std=c++20", "-O3", CERTIFICATE.with_name("expand_splice.cpp"),
                        "-o", binary], check=True)

        def check(task):
            key, groups, earlier = task
            expected = sum((6 if g.get("palindromic_upper") else 12) * len(g["caps"]) * len(g["tails"])
                           for g in groups)
            lines = [f"{cut} {key} {len(groups)} {len(earlier)} {expected}"]
            for g in groups:
                orientations = 1 if g.get("palindromic_upper") else 2
                lines.append(f"{orientations} {len(g['caps'])} {len(g['tails'])} {g['pivot']}")
                lines.extend(g["caps"])
                lines.extend(g["tails"])
            for number in earlier:
                high_middle, low = divmod(number, 3**20)
                high, middle = divmod(high_middle, 3**40)
                lines.append(f"{high} {middle} {low}")
            result = subprocess.run([binary], input="\n".join(lines), text=True,
                                    stdout=subprocess.PIPE, check=True)
            return int(result.stdout)

        with ThreadPoolExecutor(max_workers=jobs) as pool:
            return sum(pool.map(check, tasks))


def verify_expanded(data, expected, jobs=1, include_earlier=True, native=False):
    """Distinct pivot orbits partition all images, so their exact counts add."""
    tasks, earlier_count = expanded_tasks(data, include_earlier)
    if native:
        count = native_expanded_count(tasks, jobs, data["cut"])
    elif jobs == 1:
        count = sum(map(check_pivot_orbit, tasks))
    else:
        from concurrent.futures import ProcessPoolExecutor
        with ProcessPoolExecutor(max_workers=jobs) as pool:
            count = sum(pool.map(check_pivot_orbit, tasks))
    if count != expected:
        raise ValueError("expanded count differs from splice count")
    earlier = f", including all {earlier_count:,} earlier boards" if include_earlier else ""
    print(f"Checked all {count:,} full images{earlier}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path, nargs="?", default=CERTIFICATE)
    parser.add_argument("--with-extension", action="store_true",
                        help="include the additional groups and verify the combined count")
    parser.add_argument("--all", action="store_true", help="include every certificate layer, including transferred tails")
    parser.add_argument("--through-transfer", action="store_true", help="check the first four layers")
    parser.add_argument("--through-next", action="store_true", help="check the first five layers")
    parser.add_argument("--through-sixth", action="store_true", help="check the first six layers")
    parser.add_argument("--expand", action="store_true", help="also check every labeled board directly")
    parser.add_argument("--native", action="store_true", help="expand with the C++20 Cartesian checker")
    parser.add_argument("--jobs", type=int, default=1, help="parallel workers for the expanded check")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    sixth = args.all or args.through_sixth
    combined = sixth or args.through_next or args.through_transfer
    if combined:
        certificate = load_all(args.certificate, include_next=sixth or args.through_next,
                               include_sixth=sixth, include_pal=args.all)
        include_next = True if sixth else None
    else:
        certificate = json.loads(args.certificate.read_text())
        if args.with_extension:
            certificate = combine(certificate, json.loads(EXTENSION.read_text()))
        include_next = (True if uses_fifth_sources(args.certificate, certificate["groups"])
                        else False if args.certificate.name == NEXT.name else None)
    groups, caps, tails, representatives, labeled = verify(
        certificate, base_path=args.certificate if combined else CERTIFICATE, include_next=include_next)
    print(f"Verified {groups:,} groups, {caps:,} caps, and {tails:,} tails.")
    print(f"{representatives:,} disjoint symmetry families give {labeled:,} labeled boards.")
    if args.expand or args.native:
        verify_expanded(certificate, labeled, args.jobs,
                        include_earlier=combined or args.certificate.resolve() == CERTIFICATE.resolve(),
                        native=args.native)
