#!/usr/bin/env python3
"""Choose the cases for the order-ten proof and write Ten/Cases.lean.

    python3 scripts/cases.py [--limit 60000] [--keep 1000] [--part 200000] [--jobs 6]
                             [--solver /path/to/cadical]

This script is not part of the proof: Lean checks a certificate for every case it lists, and
one more showing that no table avoids all of them.  It shares no code with the Lean files.

A case first fixes the row 0*y.  In normal form that row is a permutation r with r(y) <= y + 1;
there are 512 such rows.  If CaDiCaL does not refute a case within
`--limit` conflicts, the case is divided by the value of the next entry of the column x*0.
Cases refuted in fewer than `--keep` conflicts are left out; the covering certificate handles
them.  The cases are grouped into parts of about `--part` conflicts, one Lean module each.

Variables: v(x,y,z) says x*y = z.  Clauses:
  * every cell has exactly one value;
  * every row takes every value exactly once (Equation 677 makes the rows permutations);
  * for all x,y,a,b,c:  y*x=a, a*y=b, x*b=c  imply  y*c=x          (Equation 677)
                        y*x=a, a*y=b, y*c=x  imply  x*b=c          (cancel y on the left)
                        y*x=a, x*b=c, y*c=x  imply  a*y=b          (cancel y, then x);
  * 0*y <= y + 1;
  * if 0*0 = 0, every element is idempotent.
The last says how the element 0 was chosen: a non-idempotent element if there is one.

The case list depends on the solver's conflict counts.  The script uses the CaDiCaL that ships
with Lean, as the build does, unless `--solver` names another.
"""

import argparse
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

N = 10


def var(x, y, z):
    return x * N * N + y * N + z + 1


def first_rows(prefix=()):
    """All permutations r of 0..N-1 with r(y) <= y + 1."""
    y = len(prefix)
    if y == N:
        yield prefix
        return
    for z in range(min(y + 2, N)):
        if z not in prefix:
            yield from first_rows((*prefix, z))


def formula():
    R = range(N)
    C = []
    for x in R:
        for y in R:
            C.append([var(x, y, z) for z in R])
            C += [
                [-var(x, y, z1), -var(x, y, z2)] for z1 in R for z2 in range(z1 + 1, N)
            ]
    for x in R:
        for z in R:
            C.append([var(x, y, z) for y in R])
            C += [
                [-var(x, y1, z), -var(x, y2, z)] for y1 in R for y2 in range(y1 + 1, N)
            ]
    for x in R:
        for y in R:
            for a in R:
                for b in R:
                    for c in R:
                        C.append(
                            [-var(y, x, a), -var(a, y, b), -var(x, b, c), var(y, c, x)]
                        )
                        C.append(
                            [-var(y, x, a), -var(a, y, b), -var(y, c, x), var(x, b, c)]
                        )
                        C.append(
                            [-var(y, x, a), -var(x, b, c), -var(y, c, x), var(a, y, b)]
                        )
    C += [[-var(0, y, z)] for y in R for z in R if z > y + 1]
    C += [[-var(0, 0, 0), var(x, x, x)] for x in R]
    return C


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument(
        "--limit", type=int, default=60000, help="conflicts allowed per case"
    )
    parser.add_argument(
        "--keep", type=int, default=1000, help="list cases needing this many"
    )
    parser.add_argument(
        "--part", type=int, default=200000, help="conflicts per Lean module"
    )
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--solver", help="CaDiCaL executable (defaults to Lean's copy)")
    args = parser.parse_args()
    solver = args.solver
    if not solver:
        prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        solver = str(Path(prefix) / "bin" / "cadical")
    clauses = formula()
    text = "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)

    def refute(case):
        """The cases, each with its conflict count, into which `case` is divided."""
        with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
            f.write(f"p cnf {N**3} {len(clauses) + len(case)}\n{text}")
            f.write("".join(f"{var(*entry)} 0\n" for entry in case))
        run = subprocess.run(
            [solver, "-c", str(args.limit), f.name],
            capture_output=True,
            text=True,
            check=False,
        )
        os.unlink(f.name)
        if run.returncode == 10:
            sys.exit(f"a table exists in the case {case}")
        if run.returncode == 20:
            conflicts = [
                line.split()[2]
                for line in run.stdout.splitlines()
                if line.startswith("c conflicts:")
            ]
            return [(case, int(conflicts[0]) if conflicts else 0)]
        x = 1 + sum(1 for entry in case if entry[1] == 0 and entry[0] > 0)
        return [done for z in range(N) for done in refute([*case, (x, 0, z)])]

    rows = [[(0, y, r[y]) for y in range(N)] for r in first_rows()]
    with ThreadPoolExecutor(args.jobs) as pool:
        cases = [done for found in pool.map(refute, rows) for done in found]
    kept = [(case, conflicts) for case, conflicts in cases if conflicts >= args.keep]
    parts, load = [[]], 0
    for case, conflicts in kept:
        if parts[-1] and load + conflicts > args.part:
            parts.append([])
            load = 0
        parts[-1].append(case)
        load += conflicts

    def lean(case):
        return "[" + ", ".join(f"pos {x} {y} {z}" for x, y, z in case) + "]"

    body = ",\n".join(
        "  [" + ",\n   ".join(lean(case) for case in part) + "]" for part in parts
    )
    Path("Ten/Cases.lean").write_text(f"""import Ten.Formula

/-!
# The cases

`parts` lists the cases, in the groups that one module each refutes: `Ten/Part/Pk.lean` refutes
`parts[k]!`.  The literal `pos x y z` says `x ⋆ y = z`.

This file is data and is not trusted: `Ten` checks that no table satisfying the formula avoids
all the cases.  It was written by `scripts/cases.py`, which fixes the first row and then
entries of the first column until CaDiCaL refutes the case within {args.limit} conflicts.
-/

namespace Ten

open E670

set_option maxRecDepth 100000 in
def parts : List (List Cube) := [
{body}]

end Ten
""")
    print(
        f"{len(cases)} cases found, {len(kept)} listed in {len(parts)} parts; "
        f"{sum(c for _, c in cases)} conflicts, at most {max(c for _, c in cases)} in a case"
    )
    print(
        f"Ten/Cases.lean written; now run ../E670-order-10/scripts/parts.sh {len(parts)} Ten"
    )


if __name__ == "__main__":
    main()
