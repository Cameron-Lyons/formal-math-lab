"""Replay the six-color obstruction for all deletions from [78].

Build puncture71.cpp and run, for example,
  python3 puncture78.py --solver ./puncture71 --jobs 3 --checkpoint cube-checkpoints
The positive seven-color words are checked separately by verify_deletions.py.
"""

import argparse
import random
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from itertools import combinations
from pathlib import Path

POSITIONS = set(range(74)) - {24, 29, 34}
BLOCK = tuple(range(38, 48))
EDGES = {
    tuple(a + j * d for j in range(4))
    for a in POSITIONS
    for d in range(1, (73 - a) // 3 + 1)
    if all(a + j * d in POSITIONS for j in range(4))
}


def enumerate_cubes():
    """Generate all equality patterns on the block up to color names.

    A fixed monochromatic triple in an AP already prevents completion. A
    fully fixed progression must have three colors. All other cases stay.
    """
    triples = {t for edge in EDGES for t in combinations(edge, 3)}
    block = set(BLOCK)
    required_triples = [
        [
            tuple(BLOCK.index(j) for j in t[:-1])
            for t in triples
            if t[-1] == x and set(t) <= block
        ]
        for x in BLOCK
    ]
    required_edges = [
        [
            tuple(BLOCK.index(j) for j in e[:-1])
            for e in EDGES
            if e[-1] == x and set(e) <= block
        ]
        for x in BLOCK
    ]
    patterns = []
    labels = []

    def extend(used):
        i = len(labels)
        if i == len(BLOCK):
            patterns.append("".join(map(str, labels)))
            return
        for color in range(min(used + 1, 6)):
            if any(labels[a] == labels[b] == color for a, b in required_triples[i]):
                continue
            if any(
                len({labels[a], labels[b], labels[c], color}) < 3
                for a, b, c in required_edges[i]
            ):
                continue
            labels.append(color)
            extend(max(used, color + 1))
            labels.pop()

    extend(0)
    return patterns


def independent_cubes():
    """Generate all set partitions first, then test each affected AP directly."""
    incidence = [tuple(BLOCK.index(x) for x in e if x in BLOCK) for e in EDGES]
    incidence = [e for e in incidence if len(e) >= 3]

    # 'parts' is a tuple of disjoint blocks of indices; a fresh block is appended
    # only at the end, so each unordered partition occurs once.
    def partitions(parts, i):
        if i == len(BLOCK):
            yield parts
            return
        for j in range(len(parts)):
            yield from partitions((*parts[:j], (*parts[j], i), *parts[j + 1 :]), i + 1)
        if len(parts) < 6:
            yield from partitions((*parts, (i,)), i + 1)

    possible = set()
    for parts in partitions((), 0):
        word = [""] * len(BLOCK)
        for c, subset in enumerate(parts):
            for j in subset:
                word[j] = str(c)
        # A partial quadruple with m fixed positions can eventually contain
        # at most (4-m) plus the number of currently distinct colors.
        if all(len({word[j] for j in e}) + 4 - len(e) >= 3 for e in incidence):
            possible.add("".join(word))
    return possible


def check_embeddings():
    # The published [54] obstruction handles the outer deletions. This program
    # checks the 71-point obstruction on [74] for the remaining positions.
    holes = set()
    for shape in (set(range(54)), POSITIONS):
        for shift in range(78 - max(shape)):
            image = {x + shift for x in shape}
            holes.update(set(range(78)) - image)
            holes.update(set(range(78)) - {77 - x for x in image})
    if holes != set(range(78)):
        raise ValueError("some deletion lacks an embedding")


def line(word):
    return "0 " + "." * BLOCK[0] + word + "." * (73 - BLOCK[-1])


def validate(lines, expected):
    if len(lines) != len(expected):
        raise ValueError("wrong number of cube results")
    nodes = 0
    for row, case in zip(lines, expected, strict=True):
        fields = row.split()
        if len(fields) != 4 or fields[0] != "UNSAT" or " ".join(fields[2:]) != case:
            raise ValueError(f"unexpected solver result: {row}")
        visited = int(fields[1])
        if visited < 1:
            raise ValueError("invalid node count")
        nodes += visited
    return nodes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", type=Path, default=Path("./puncture71"))
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--checkpoint", type=Path, default=Path("cube-checkpoints"))
    parser.add_argument("--audit-only", action="store_true")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("jobs must be positive")
    check_embeddings()
    words = enumerate_cubes()
    independent = independent_cubes()
    if (
        len(words) != len(set(words))
        or len(words) != 17855
        or set(words) != independent
    ):
        raise ValueError("independent cube enumeration disagrees")
    random.Random(811).shuffle(words)
    inputs = [line(w) for w in words]
    chunks = [inputs[i : i + 24] for i in range(0, len(inputs), 24)]
    checkpoint = args.checkpoint
    checkpoint.mkdir(exist_ok=True, parents=True)
    solver = args.solver.resolve()
    started = time.monotonic()

    def verify_chunk(i):
        file = checkpoint / f"chunk-{i:04d}.txt"
        if file.exists():
            return validate(file.read_text().splitlines(), chunks[i])
        if args.audit_only:
            raise ValueError(f"missing checkpoint {file.name}")
        outcome = subprocess.run(
            [str(solver)],
            input="\n".join(chunks[i]) + "\n",
            text=True,
            capture_output=True,
            check=True,
        )
        nodes = validate(outcome.stdout.splitlines(), chunks[i])
        temporary = file.with_suffix(".tmp")
        temporary.write_text(outcome.stdout)
        temporary.replace(file)
        return nodes

    with ThreadPoolExecutor(args.jobs) as pool:
        tasks = [pool.submit(verify_chunk, i) for i in range(len(chunks))]
        for number, task in enumerate(as_completed(tasks), 1):
            task.result()
            if number % 50 == 0:
                print(
                    f"{number}/{len(chunks)} chunks, {time.monotonic() - started:.1f} s",
                    flush=True,
                )

    # Audit the assembled checkpoint files from disk. Compare complete cube
    # identifiers, including those in any checkpoint inherited from a prior run.
    expected_files = {f"chunk-{i:04d}.txt" for i in range(len(chunks))}
    if {p.name for p in checkpoint.glob("chunk-*.txt")} != expected_files:
        raise ValueError("unexpected checkpoint file list")
    seen = []
    nodes = 0
    for i, chunk in enumerate(chunks):
        results = (checkpoint / f"chunk-{i:04d}.txt").read_text().splitlines()
        nodes += validate(results, chunk)
        seen.extend(" ".join(row.split()[2:]) for row in results)
    if len(seen) != len(set(seen)) or set(seen) != set(inputs):
        raise ValueError("duplicate or missing cube")
    print(f"All {len(seen)} cubes are UNSAT in {nodes} search nodes.")
    print("Every deletion from [78] contains a six-color obstruction.")


if __name__ == "__main__":
    main()
