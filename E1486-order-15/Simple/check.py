"""Decide the E1486 graph problem using Python 3 and CaDiCaL.

    python3 Simple/check.py 9 11 13 15
    python3 Simple/check.py --verify-with /path/to/lrat-trim 15
    python3 Simple/check.py --pattern 6:2 26

The optional checker replays each UNSAT proof against its input CNF.
A pattern K:J restricts the search to K squares, J of them fixed by squaring.
"""

import argparse
import itertools
import shutil
import subprocess
import tempfile
from pathlib import Path


class CNF:
    def __init__(self):
        self.variables = 0
        self.clauses = []

    def fresh(self):
        self.variables += 1
        return self.variables

    def add(self, *clause):
        self.clauses.append(clause)

    def lex_ge(self, left, right):
        # Forbid a first difference of 0 versus 1. Each auxiliary bit records
        # that the preceding bits agree. Implications toward this bit suffice.
        guard = []
        for x, y in zip(left, right, strict=False):
            if x != y:
                self.add(*guard, x, -y)
                equal = self.fresh()
                self.add(*guard, -x, -y, equal)
                self.add(*guard, x, y, equal)
                guard = [-equal]

    def write(self, path):
        with path.open("w") as output:
            print("p cnf", self.variables, len(self.clauses), file=output)
            for clause in self.clauses:
                print(*clause, 0, file=output)


def graph_formula(n, k, j):
    """The first k vertices are squares. The first j squares are fixed."""
    f = CNF()
    vertices, squares = range(n), range(k)
    edge = [[f.fresh() for _ in vertices] for _ in vertices]

    # Exactly the squares are on closed walks of length two. On these walks,
    # each square meets itself or its assigned partner.
    for q in squares:
        partner = q if q < j else j + ((q - j) ^ 1)
        f.add(edge[q][partner])
    for a in range(k, n):
        f.add(-edge[a][a])
        for b in range(a):
            f.add(-edge[a][b], -edge[b][a])
        f.add(*(edge[q][a] for q in squares))  # A square predecessor for a.

    # Two distinct midpoints cannot share both a predecessor and a successor.
    for a, b in itertools.combinations(vertices, 2):
        common_predecessor = f.fresh()
        for v in vertices:
            f.add(-edge[v][a], -edge[v][b], common_predecessor)
            f.add(-edge[a][v], -edge[b][v], -common_predecessor)

    # Every square is accessible in two steps from every starting vertex.
    for v in vertices:
        for q in squares:
            witnesses = []
            for a in vertices:
                midpoint = f.fresh()
                f.add(-midpoint, edge[v][a])
                f.add(-midpoint, edge[a][q])
                witnesses.append(midpoint)
            f.add(*witnesses)

    # Maximize the square adjacency matrix under relabeling that respects the
    # assigned partners. These swaps all preserve the fixed-point/pair pattern.
    pairs = range(j, k, 2)
    swaps = [[(a, b)] for a, b in itertools.combinations(range(j), 2)]
    swaps += [[(a, a + 1)] for a in pairs]
    swaps += [[(a, b), (a + 1, b + 1)] for a, b in itertools.combinations(pairs, 2)]
    matrix = [edge[a][b] for a in squares for b in squares]
    for transpositions in swaps:
        perm = list(squares)
        for a, b in transpositions:
            perm[a], perm[b] = perm[b], perm[a]
        f.lex_ge(matrix, [edge[perm[a]][perm[b]] for a in squares for b in squares])

    # After fixing the square labels, sort the remaining vertices by the bits
    # of their incoming and outgoing square edges. This leaves matrix intact.
    def profile(v):
        return [edge[q][v] for q in squares] + [edge[v][q] for q in squares]

    for a in range(k, n - 1):
        f.lex_ge(profile(a), profile(a + 1))
    return f, edge


def verify_model(model, edge):
    """Recover an operation from a SAT witness and check E1486 directly."""
    n = len(edge)
    vertices = range(n)
    out = [{b for b in vertices if edge[a][b] in model} for a in vertices]
    square = {q for q in vertices if any(q in out[a] for a in out[q])}
    table = []
    for x in vertices:
        row = []
        for y in vertices:
            middle = [a for a in out[x] if y in out[a]]
            if len(middle) > 1:
                raise ValueError("two different midpoints")
            if middle:
                row.append(middle[0])
            else:
                row.append(next(q for q in square if y in out[q]))
        table.append(row)
    if any(
        table[table[y][x]][table[x][table[z][z]]] != x
        for x, y, z in itertools.product(vertices, repeat=3)
    ):
        raise ValueError("the reconstructed table violates E1486")


def solve(n, solver, checker, pattern=None):
    cases = 0
    with tempfile.TemporaryDirectory() as tmp:
        cnf, proof = (Path(tmp) / name for name in ("graph.cnf", "proof.lrat"))
        for k in range(1, n + 1):
            for j in range(k % 2, k + 1, 2):
                if pattern and (k, j) != pattern:
                    continue
                cases += 1
                formula, edges = graph_formula(n, k, j)
                formula.write(cnf)
                args = (
                    [solver, "-q", "--lrat", cnf, proof]
                    if checker
                    else [solver, "-q", cnf]
                )
                run = subprocess.run(args, capture_output=True, text=True, check=False)
                if run.returncode == 10:
                    model = {
                        int(t)
                        for line in run.stdout.splitlines()
                        if line.startswith("v ")
                        for t in line.split()[1:]
                    }
                    verify_model(model, edges)
                    print(
                        f"order {n}: model verified on all {n**3} triples (k={k}, j={j})",
                        flush=True,
                    )
                    return
                if run.returncode != 20:
                    raise RuntimeError(f"CaDiCaL failed for k={k}, j={j}\n{run.stderr}")
                if checker:
                    replay = subprocess.run(
                        [checker, "--rup", cnf, proof],
                        capture_output=True,
                        text=True,
                        check=False,
                    )
                    if replay.returncode != 20:
                        raise RuntimeError(
                            f"LRAT verification failed for k={k}, j={j}\n{replay.stdout}\n{replay.stderr}"
                        )
    result = "RUP proofs verified" if checker else "UNSAT"
    print(f"order {n}: {cases} cases, all {result}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("orders", nargs="*", type=int, default=[15])
    parser.add_argument(
        "--solver", help="CaDiCaL executable (defaults to PATH or Lean's copy)"
    )
    parser.add_argument(
        "--verify-with",
        metavar="EXECUTABLE",
        help="independently check binary RUP proofs using lrat-trim",
    )
    parser.add_argument(
        "--pattern",
        metavar="K:J",
        help="check only K squares with J of them fixed by squaring",
    )
    args = parser.parse_args()
    pattern = None
    if args.pattern:
        try:
            k, j = (int(part) for part in args.pattern.split(":"))
        except ValueError:
            parser.error("--pattern must have the form K:J")
        if not 0 <= j <= k or (k - j) % 2:
            parser.error("--pattern needs 0 <= J <= K with K - J even")
        pattern = (k, j)
    solver = args.solver or shutil.which("cadical")
    if solver is None or not solver:
        prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        solver = str(Path(prefix) / "bin" / "cadical")
    for n in args.orders:
        if n < 1:
            parser.error("orders must be positive")
        if pattern and not 1 <= pattern[0] <= n:
            parser.error("--pattern needs 1 <= K <= order")
        solve(n, solver, args.verify_with, pattern)


if __name__ == "__main__":
    main()
