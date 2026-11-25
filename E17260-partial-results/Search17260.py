"""Search finite operation tables for E17260, using SMT enumeration sorts."""

import argparse
import json
import time

import z3


def search(n, timeout):
    U, es = z3.EnumSort("U" + str(n), ["e" + str(n) + "_" + str(i) for i in range(n)])
    op = z3.Function("op" + str(n), U, U, U)
    s = z3.Solver()
    s.set(timeout=timeout * 1000)
    for x in es:
        for y in es:
            for z in es:
                s.add(x == op(op(y, x), op(z, op(x, op(z, z)))))
    # Every diagonal entry is conjugate under relabeling; pin the first to 0 or 1.
    s.add(z3.Or(op(es[0], es[0]) == es[0], op(es[0], es[0]) == es[1]))
    t = time.time()
    r = s.check()
    print(
        json.dumps(
            {"order": n, "result": str(r), "seconds": round(time.time() - t, 3)}
        ),
        flush=True,
    )
    if r == z3.sat:
        m = s.model()
        table = [[es.index(m.eval(op(a, b))) for b in es] for a in es]
        assert all(
            x == table[table[y][x]][table[z][table[x][table[z][z]]]]
            for x in range(n)
            for y in range(n)
            for z in range(n)
        )
        print(json.dumps(table), flush=True)
        with open("Model17260.json", "w") as f:
            f.write(json.dumps(table))
        return True
    return False


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--min", type=int, default=2)
    ap.add_argument("--max", type=int, default=12)
    ap.add_argument("--timeout", type=int, default=60)
    a = ap.parse_args()
    for n in range(a.min, a.max + 1):
        if search(n, a.timeout):
            break
