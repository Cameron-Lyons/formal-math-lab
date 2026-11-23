"""Replay one or more splice groups from their recorded six-row discovery prefixes."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from verify_splice import (CERTIFICATE, canonical_palindromic_prefix, extension_checkpoints,
                           extension_source, patterns, previous_layers, reflected_rows,
                           split_rows, uses_fifth_sources)


def upper_sections(lower, remaining):
    """Produce every upper section, including lower, using precisely remaining."""
    if len(lower) == 1:
        if not remaining:
            yield lower
        return

    def choose_top(top, unused):
        j = len(top)
        if j + 2 == len(lower):
            for section in upper_sections(top, unused):
                yield section + lower
            return
        triple = tuple(lower[j:j+3])
        for color in "012":
            pattern = (color, *triple)
            if pattern in unused:
                yield from choose_top(top + color, unused - {pattern})

    yield from choose_top("", remaining)


def replay(binary, group, index, exhaust, sources=None, after=None):
    original = None
    if "extends" in group:
        original = extension_source(group, sources)
        if after is None:
            after = extension_checkpoints([group], sources)[0]
    if "row6_sample" in group and original is None:
        from reproduce_symmetric import replay_group
        replay_group(binary, group)
        print(f"Group {index} matched its sampled cap and tail lists.", flush=True)
        return
    prefix = group["prefix"]
    rows = split_rows(prefix, 0, 6)
    if rows[-1] != group["pivot"]:
        raise ValueError(f"group {index} has a different discovery pivot")
    caps = sorted(section[:25] for section in upper_sections(rows[-1], patterns(rows, 0)))
    if group.get("palindromic_upper"):
        caps = [c for c in caps if canonical_palindromic_prefix(split_rows(c + rows[-1], 0, 6))]
    elif group.get("mirror_closure"):
        caps = [c for c in caps if c < reflected_rows(c, 0, 5)]
    if original is not None:
        # A transferred or reflection-reduced source can retain a subset of all caps.
        caps = [c for c in caps if c in original["caps"]]
    if caps != group["caps"]:
        raise ValueError(f"group {index} cap mismatch")
    limit = 0 if exhaust else group.get("search_limit", len(group["tails"]))
    if "row6_sample" in group:
        from reproduce_symmetric import find_tails
        tails = [t for t in find_tails(binary, prefix, group["row6_sample"]) if t > after]
        if limit:
            tails = tails[:limit]
    else:
        command = [binary, prefix, str(limit)]
        if after is not None:
            command.extend(["--after", after])
        result = subprocess.run(command, check=True, text=True, stdout=subprocess.PIPE)
        boards = result.stdout.splitlines()
        if any(not b.startswith(prefix) for b in boards):
            raise ValueError(f"group {index} returned a different discovery prefix")
        tails = [b[len(prefix):] for b in boards]
    if group.get("mirror_closure") or group.get("palindromic_upper"):
        tails = sorted(set(tails) | {reflected_rows(t, 6, 10) for t in tails})
        if after is not None:
            tails = [t for t in tails if t > after]
    if tails != group["tails"]:
        raise ValueError(f"group {index} tail mismatch")
    print(f"Group {index} matched both witness lists ({len(caps):,} × {len(group['tails']):,}).",
          flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("groups", type=int, nargs="*", help="one-based group numbers, default all")
    parser.add_argument("--certificate", type=Path, default=CERTIFICATE,
                        help="witness file containing the discovery prefixes")
    parser.add_argument("--exhaust", action="store_true",
                        help="exhaust the entire prefix for unsampled groups, or the recorded sample for sampled groups")
    parser.add_argument("--jobs", type=int, default=1, help="number of simultaneous prefix searches")
    args = parser.parse_args()
    groups = json.loads(args.certificate.read_text())["groups"]
    indices = args.groups or list(range(1, len(groups)+1))
    if args.jobs < 1 or any(i < 1 or i > len(groups) for i in indices):
        parser.error("choose a positive job count and valid group numbers")
    sources = None
    if any("extends" in groups[i-1] for i in indices):
        sources = previous_layers(include_next=uses_fifth_sources(args.certificate, groups))
    checkpoints = extension_checkpoints(groups[:max(indices)], sources) if sources is not None else {}
    with TemporaryDirectory() as directory:
        binary = Path(directory) / "splice_search"
        subprocess.run(["c++", "-O3", "-std=c++20", CERTIFICATE.with_name("splice_search.cpp"),
                        "-o", binary], check=True)
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            results = [pool.submit(replay, binary, groups[i-1], i, args.exhaust,
                                   sources, checkpoints.get(i-1)) for i in indices]
            for result in results:
                result.result()


if __name__ == "__main__":
    main()
