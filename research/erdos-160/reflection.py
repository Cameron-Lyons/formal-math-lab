"""Generate or solve the seven-color problem with reversal acting by a color permutation."""

import argparse
import shutil
import subprocess
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory


def encode(length, swaps):
    half = (length + 1) // 2
    palette = range(7)
    permutation = [c ^ 1 if c < 2 * swaps else c for c in palette]
    positions = [(min(i, length - 1 - i), 2 * i >= length) for i in range(length)]
    clauses = []
    seen = set()

    def add(literals):
        row = tuple(sorted(set(literals)))
        if row not in seen and not any(-v in row for v in row):
            clauses.append(row)
            seen.add(row)

    def variable(i, c):
        return 1 + 7 * i + c

    def has_color(i, c):
        j, reflected = positions[i]
        return variable(j, permutation[c] if reflected else c)

    for i in range(half):
        choices = [variable(i, c) for c in palette]
        add(choices)
        for a, b in combinations(choices, 2):
            add([-a, -b])
    if length % 2:
        for c in range(2 * swaps):
            add([-variable(half - 1, c)])

    # Name the transposed pairs and the fixed colors in order of first occurrence
    # from the center outward. Orient each pair at its first occurrence.
    order = list(reversed(range(half)))
    for c in palette:
        if c < 2 * swaps and c % 2 == 0:
            predecessor = c - 2
        elif c < 2 * swaps or c > 2 * swaps:
            predecessor = c - 1
        else:
            continue
        if predecessor < 0:
            continue
        for j, i in enumerate(order):
            add([-variable(i, c)] + [variable(k, predecessor) for k in order[:j]])

    equalities = {}

    def equal(i, j):
        u, left = positions[i]
        v, right = positions[j]
        opposite = left != right
        key = (min(u, v), max(u, v), opposite)
        if key not in equalities:
            z = 7 * half + len(equalities) + 1
            equalities[key] = z
            for c in palette:
                a = variable(u, c)
                b = variable(v, permutation[c] if opposite else c)
                add([-a, -b, z])
                add([-a, b, -z])
                add([a, -b, -z])
        return equalities[key]

    progressions = [
        (a, a + d, a + 2 * d, a + 3 * d)
        for d in range(1, (length - 1) // 3 + 1)
        for a in range(length - 3 * d)
    ]
    for ap in progressions:
        # A four-tuple has at least three colors iff at most one of its six
        # unordered pairs has equal colors. A repeated indicator becomes a unit clause.
        pairs = [equal(i, j) for i, j in combinations(ap, 2)]
        for p, q in combinations(pairs, 2):
            add([-p, -q])
        for triple in combinations(ap, 3):
            for c in palette:
                add([-has_color(i, c) for i in triple])
    return 7 * half + len(equalities), clauses, has_color, progressions, permutation


def write_dimacs(filename, variables, clauses):
    with filename.open("w") as out:
        print("p cnf", variables, len(clauses), file=out)
        for row in clauses:
            print(*row, 0, file=out)


def solve(length, swaps, filename, solver, enumerate_all=False):
    variables, clauses, has_color, progressions, permutation = encode(length, swaps)
    number = 0
    while True:
        write_dimacs(filename, variables, clauses)
        if solver is None:
            return
        result = subprocess.run(
            [solver, "-q", "--check", filename],
            check=False,
            capture_output=True,
            text=True,
        )
        lines = result.stdout.splitlines()
        if result.returncode == 20 and "s UNSATISFIABLE" in lines:
            if enumerate_all:
                print(f"N={length} transpositions={swaps} count={number}")
            else:
                print(f"N={length} transpositions={swaps} UNSAT")
            return
        if result.returncode != 10 or "s SATISFIABLE" not in lines:
            raise RuntimeError(
                result.stderr or result.stdout or f"solver exit {result.returncode}"
            )
        model = {
            int(v) for line in lines if line.startswith("v ") for v in line.split()[1:]
        }
        word = [
            next(c for c in range(7) if has_color(i, c) in model) for i in range(length)
        ]
        if any(permutation[c] != word[length - 1 - i] for i, c in enumerate(word)):
            raise ValueError("witness fails reversal symmetry")
        if any(len({word[i] for i in ap}) < 3 for ap in progressions):
            raise ValueError("witness fails a progression")
        number += 1
        print(f"N={length} transpositions={swaps} SAT")
        print("".join(map(str, word)), flush=True)
        if not enumerate_all:
            return
        clauses.append(tuple(-has_color(i, word[i]) for i in range((length + 1) // 2)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("length", type=int)
    parser.add_argument("swaps", type=int, choices=range(4))
    parser.add_argument("--dimacs", type=Path, help="write the CNF and exit")
    parser.add_argument(
        "--all", action="store_true", help="enumerate every canonical coloring"
    )
    parser.add_argument("--solver", help="path to the CaDiCaL executable")
    args = parser.parse_args()
    if args.length < 1:
        parser.error("length must be positive")
    if args.dimacs:
        solve(args.length, args.swaps, args.dimacs, None)
        return
    solver = args.solver or shutil.which("cadical")
    if solver is None:
        lean = shutil.which("lean")
        if lean is None:
            parser.error("specify --solver or make CaDiCaL available through Lean")
        prefix = subprocess.check_output([lean, "--print-prefix"], text=True).strip()
        solver = Path(prefix) / "bin" / "cadical"
    with TemporaryDirectory() as tmp:
        solve(args.length, args.swaps, Path(tmp) / "reflection.cnf", solver, args.all)


if __name__ == "__main__":
    main()
