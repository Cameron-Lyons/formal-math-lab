#!/usr/bin/env python3
"""Independent check that equation 670 has no model with ten elements.

    python3 scripts/check.py [--jobs N] [--verify-with /path/to/drat-trim]

This script shares no code with the Lean development.  It writes the formula directly from the
law and splits it by the first row of the table.  In normal form the first row r is a permutation
with r(y) <= y + 1; there are 512 such rows, found here by enumeration.  For each of them the
script runs CaDiCaL and reports the verdict.  With `--verify-with` every refutation is also checked
by drat-trim.

Variables: v(x,y,z) says x*y = z.  Clauses:
  * every cell has exactly one value;
  * every row takes every value exactly once (rows of a finite model are permutations);
  * for all x,y,a,b,c:  x*y=a, a*y=b, x*b=c  imply  y*c=x          (the law)
                        x*y=a, a*y=b, y*c=x  imply  x*b=c          (cancel y on the left)
                        x*y=a, x*b=c, y*c=x  imply  a*y=b          (cancel y, then x);
  * if 0*0 = 0, every element is idempotent (the element called 0 is non-idempotent if any is);
  * row 0 is the given row.
"""
import argparse, os, shutil, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

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
            yield from first_rows(prefix + (z,))


def formula():
    R = range(N)
    C = []
    for x in R:
        for y in R:
            C.append([var(x, y, z) for z in R])
            C += [[-var(x, y, z1), -var(x, y, z2)] for z1 in R for z2 in range(z1 + 1, N)]
    for x in R:
        for z in R:
            C.append([var(x, y, z) for y in R])
            C += [[-var(x, y1, z), -var(x, y2, z)] for y1 in R for y2 in range(y1 + 1, N)]
    for x in R:
        for y in R:
            for a in R:
                for b in R:
                    for c in R:
                        p1, p2, p3, p4 = var(x, y, a), var(a, y, b), var(x, b, c), var(y, c, x)
                        C.append([-p1, -p2, -p3, p4])
                        C.append([-p1, -p2, -p4, p3])
                        C.append([-p1, -p3, -p4, p2])
    C += [[-var(0, 0, 0), var(x, x, x)] for x in R]
    return C


def find_cadical():
    exe = shutil.which("cadical")
    if exe:
        return exe
    lean = shutil.which("lean")
    if lean:
        try:
            prefix = subprocess.run([lean, "--print-prefix"], capture_output=True, text=True).stdout.strip()
            cand = os.path.join(prefix, "bin", "cadical")
            if os.path.exists(cand):
                return cand
        except OSError:
            pass
    sys.exit("cadical not found on PATH or in the Lean toolchain")


def check_law(T):
    return all(T[y][T[x][T[T[x][y]][y]]] == x for x in range(N) for y in range(N))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--verify-with", metavar="DRAT_TRIM")
    ap.add_argument("--jobs", type=int, default=1)
    args = ap.parse_args()
    cadical = find_cadical()
    base = formula()
    body = "".join(" ".join(map(str, c)) + " 0\n" for c in base)
    rows = list(first_rows())
    tmp = tempfile.mkdtemp(prefix="e670-")

    def run(row):
        tag = "".join(map(str, row))
        cnf = os.path.join(tmp, tag + ".cnf")
        proof = os.path.join(tmp, tag + ".drat")
        with open(cnf, "w") as fh:
            fh.write(f"p cnf {N ** 3} {len(base) + N}\n" + body)
            fh.write("".join(f"{var(0, y, z)} 0\n" for y, z in enumerate(row)))
        cmd = [cadical, "-q", cnf] + ([proof] if args.verify_with else [])
        t0 = time.time()
        out = subprocess.run(cmd, capture_output=True, text=True).stdout
        dt = time.time() - t0
        if "s SATISFIABLE" in out:
            lits = [int(t) for line in out.splitlines() if line.startswith("v ") for t in line[2:].split()]
            T = [[-1] * N for _ in range(N)]
            for l in lits:
                if 0 < l <= N ** 3:
                    l -= 1
                    T[l // (N * N)][(l // N) % N] = l % N
            return row, "SAT", dt, f"law holds: {check_law(T)}; table {T}"
        if "s UNSATISFIABLE" not in out:
            return row, "UNKNOWN", dt, ""
        note = ""
        if args.verify_with:
            res = subprocess.run([args.verify_with, cnf, proof], capture_output=True, text=True).stdout
            note = "proof verified" if "s VERIFIED" in res else "PROOF NOT VERIFIED"
            os.unlink(proof)
        os.unlink(cnf)
        return row, "UNSAT", dt, note

    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for row, status, dt, note in pool.map(run, rows):
            print(f"{' '.join(map(str, row))}  {status:7} {dt:7.2f}s  {note}", flush=True)
            results.append((status, note))
    shutil.rmtree(tmp, ignore_errors=True)
    unsat = sum(1 for s, _ in results if s == "UNSAT")
    if unsat == len(rows) and all("NOT" not in n for _, n in results):
        tail = ", all proofs verified" if args.verify_with else ""
        print(f"order 10: {len(rows)} first rows, all UNSAT{tail}")
    else:
        print(f"order 10: {unsat} of {len(rows)} first rows UNSAT")
        sys.exit(1)


if __name__ == "__main__":
    main()
