"""Compact SAT search for E17260. SAT/UNSAT output is not a Lean proof.

Optional cycle pruning uses separately derived necessary conditions:
nontrivial models have neither fixed points nor 2-cycles under x -> x*x.
With --cycle K, only models possessing a square cycle of length K are searched.
"""
import argparse
import json
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def search(n, conflicts, cycle=0, prune_cycles=False):
    started = time.monotonic()
    pool = IDPool()
    f = [[[pool.id(('f', a, b, c)) for c in range(n)]
          for b in range(n)] for a in range(n)]
    c = [[pool.id(('c', x, a)) for a in range(n)] for x in range(n)]
    t = [[pool.id(('t', x, b)) for b in range(n)] for x in range(n)]
    u = [[[pool.id(('u', x, z, a)) for a in range(n)]
          for z in range(n)] for x in range(n)]
    count = 0
    with Solver(name='cadical195') as solver:
        def add(clause):
            nonlocal count
            solver.add_clause(clause)
            count += 1

        def exactly_one(literals):
            for clause in CardEnc.equals(literals, bound=1, vpool=pool,
                                         encoding=EncType.seqcounter).clauses:
                add(clause)

        for row in f:
            for cell in row:
                exactly_one(cell)
        if prune_cycles:
            for a in range(n):
                add([-f[a][a][a]])
                for b in range(a + 1, n):
                    add([-f[a][a][b], -f[b][b][a]])
            add([f[0][0][1]])
        if cycle:
            for a in range(cycle):
                add([f[a][a][(a + 1) % cycle]])
        else:
            # Canonical discovery order in row 0; safe under relabeling.
            for j in range(n):
                for v in range(j + 2, n):
                    add([-f[0][j][v]])
        for x in range(n):
            for a in range(n):
                add([-c[x][a]] + [f[y][x][a] for y in range(n)])
                for y in range(n):
                    add([-f[y][x][a], c[x][a]])
                for b in range(n):
                    # C_x * T_x = {x}.
                    add([-c[x][a], -t[x][b], f[a][b][x]])
            for z in range(n):
                exactly_one(u[x][z])
                for d in range(n):
                    for a in range(n):
                        add([-f[z][z][d], -f[x][d][a], u[x][z][a]])
                for a in range(n):
                    for b in range(n):
                        add([-u[x][z][a], -f[z][a][b], t[x][b]])
        context = {'order': n, 'cycle': cycle,
                   'prune_cycles': prune_cycles, 'conflict_budget': conflicts}
        print(json.dumps(dict(context, vars=pool.top, clauses=count,
                              setup_seconds=time.monotonic() - started)), flush=True)
        solver.conf_budget(conflicts)
        result = solver.solve_limited(expect_interrupt=False)
        state = 'sat' if result else 'unsat' if result is False else 'unknown'
        print(json.dumps(dict(context, result=state,
                              seconds=time.monotonic() - started,
                              stats=solver.accum_stats())), flush=True)
        if result:
            model = set(solver.get_model())
            table = [[next(v for v in range(n) if f[a][b][v] in model)
                      for b in range(n)] for a in range(n)]
            assert all(x == table[table[y][x]][table[z][table[x][table[z][z]]]]
                       for x in range(n) for y in range(n) for z in range(n))
            with open('Model17260.json', 'w') as handle:
                json.dump(table, handle)
            print(json.dumps(table), flush=True)
            return True
    return False


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--min', type=int, default=11)
    parser.add_argument('--max', type=int, default=11)
    parser.add_argument('--conflicts', type=int, default=50000)
    parser.add_argument('--cycle', type=int, default=0)
    parser.add_argument('--prune-cycles', action='store_true')
    args = parser.parse_args()
    if args.min < 2 or args.max < args.min or args.conflicts < 1:
        parser.error('Require 2 <= min <= max and a positive conflict budget.')
    if args.cycle != 0 and not 1 <= args.cycle <= args.min:
        parser.error('Cycle must be zero, or between 1 and the minimum order.')
    for size in range(args.min, args.max + 1):
        if search(size, args.conflicts, args.cycle, args.prune_cycles):
            break
