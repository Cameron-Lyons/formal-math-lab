#!/usr/bin/env python3
"""Seek a board with uniform 3-coordinate marginals but nonuniform T patterns.

A SAT model disproves the proposed marginal shortcut. A timeout proves nothing.
Requires python-sat (the recorded run used /tmp/exact_structure_venv).
"""
import argparse
import itertools
import json
from pathlib import Path
import threading
import time
from collections import Counter

from exact_count_cnf import CNF
from exact_marginal_cnf import FunctionalGates, negate
from exact_phase import board_model, default_board
from pysat.solvers import Solver


def build(colors, rows, prefix_rows, require_counterexample=True):
    height = colors * colors + 1
    flat = [int(x) for row in rows for x in row]
    cnf = CNF()
    cells = {p: [cnf.variable() for _ in range(colors)] for p in range(height * height)}
    for indicators in cells.values():
        cnf.add(indicators)
        for a, b in itertools.combinations(indicators, 2):
            cnf.add([-a, -b])
    for p in range(prefix_rows * prefix_rows):
        cnf.add([cells[p][flat[p]]])
    windows = [((r-1)**2+j, r*r+j, r*r+j+1, r*r+j+2)
               for r in range(1, height) for j in range(2*r-1)]
    gates = FunctionalGates(cnf)
    triple = {}
    for omit in range(4):
        axes = [a for a in range(4) if a != omit]
        for pattern in itertools.product(range(colors), repeat=3):
            indicators = []
            for i, w in enumerate(windows):
                literal = True
                for a, c in zip(axes, pattern):
                    literal = gates.and_gate(literal, cells[w[a]][c])
                triple[omit, pattern, i] = literal
                indicators.append(literal)
            gates.exactly(indicators, colors, 'sequential')
    missing = []
    for pattern in itertools.product(range(colors), repeat=4):
        present = False
        for i, w in enumerate(windows):
            occurrence = gates.and_gate(triple[3, pattern[:3], i], cells[w[3]][pattern[3]])
            present = gates.or_gate(present, occurrence)
        missing.append(negate(present))
    phases = board_model(cnf, cells, rows)
    if require_counterexample:
        cnf.add(missing)
    return cnf, cells, phases


def audit(rows, colors):
    height = colors*colors+1
    patterns = [(int(rows[r-1][j]),) + tuple(map(int, rows[r][j:j+3]))
                for r in range(1, height) for j in range(2*r-1)]
    counts = Counter(patterns)
    for omit in range(4):
        marg = Counter(p[:omit]+p[omit+1:] for p in patterns)
        assert len(marg) == colors**3 and set(marg.values()) == {colors}
    assert len(counts) != colors**4
    return {'distinct_patterns': len(counts),
            'histogram_of_multiplicities': dict(sorted(Counter(counts.values()).items())),
            'missing_patterns': [''.join(map(str,p)) for p in itertools.product(range(colors), repeat=4)
                                 if p not in counts]}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--colors', type=int, choices=[2,3], default=3)
    ap.add_argument('--prefix-rows', type=int, default=0)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--seconds', type=float, default=120)
    ap.add_argument('--solver', choices=['g4', 'm22'], default='g4')
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    if not 0 <= args.prefix_rows <= args.colors**2+1:
        ap.error('--prefix-rows must lie within the board')
    if args.seconds <= 0:
        ap.error('--seconds must be positive')
    rows = default_board(args.colors, args.seed)
    started = time.monotonic()
    cnf, cells, phases = build(args.colors, rows, args.prefix_rows)
    print(json.dumps({'event':'built','variables':cnf.variables,'clauses':len(cnf.clauses),
                      'colors':args.colors,'prefix_rows':args.prefix_rows,
                      'build_seconds':time.monotonic()-started}), flush=True)
    with Solver(name=args.solver, bootstrap_with=cnf.clauses) as solver:
        # Probe the required API before starting. CaDiCaL's Python interrupt
        # method is unsupported in python-sat 1.9.dev24, so it is not offered.
        solver.interrupt()
        solver.clear_interrupt()
        solver.set_phases([v if phases[v] else -v for v in range(1, len(phases))])
        timer = threading.Timer(args.seconds, solver.interrupt)
        started = time.monotonic(); timer.start()
        try:
            result = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        data = {'status':'SAT' if result is True else 'UNSAT' if result is False else 'UNKNOWN',
                'colors':args.colors,'prefix_rows':args.prefix_rows,'seed':args.seed,'solver':args.solver,
                'seconds':time.monotonic()-started, 'stats':solver.accum_stats()}
        if result:
            positive = set(v for v in solver.get_model() if v>0)
            flat = [next(c for c,v in enumerate(cells[p]) if v in positive) for p in range(len(cells))]
            found = [''.join(map(str,flat[r*r:(r+1)**2])) for r in range(args.colors**2+1)]
            data['rows'] = found
            data['audit'] = audit(found, args.colors)
        print(json.dumps(data), flush=True)
        if args.output:
            args.output.write_text(json.dumps(data,indent=2)+'\n')


if __name__ == '__main__':
    main()
