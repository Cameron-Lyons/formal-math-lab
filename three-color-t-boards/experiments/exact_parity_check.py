#!/usr/bin/env python3
"""Validate functional parity circuits and ordinary exact T-board counts."""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import tempfile
import time

from exact_count_cnf import CNF
from exact_marginal_check import exact_count
from exact_parity_cnf import ParityGates, make_parity_cnf, rephase_parity, write_parity
from exact_phase import board_model, default_board, normalize_board, propagate_model

ROOT = Path(__file__).resolve().parents[1]


def gate_checks():
    checked = 0
    for layout,n,negated_pair,rhs in itertools.product(('chain','tree'),range(7),(False,True),(False,True)):
        cnf = CNF()
        inputs = [cnf.variable() for _ in range(n)]
        literals = inputs + ([-inputs[0],inputs[0]] if negated_pair and n else [])
        ParityGates(cnf).require_xor(literals,rhs,layout)
        for values in itertools.product((False,True),repeat=n):
            initial = dict(zip(inputs,values))
            expected = bool(sum(initial[abs(lit)] == (lit > 0) for lit in literals) % 2) == rhs
            try:
                propagate_model(cnf,initial)
                actual = True
            except ValueError as error:
                if 'undetermined' in str(error):
                    raise
                actual = False
            assert actual == expected,(layout,n,literals,rhs,values)
            checked += 1
    return checked


def linear_structure():
    results = []
    for connected,expected in [(False,81),(True,169)]:
        cnf,_,_ = make_parity_cnf(3,orbit_canonical=True,layout='native',connected=connected)
        pivots = {}
        for variables,_ in cnf.native_xors:
            value = sum(1 << v for v in variables)
            while value:
                pivot = value.bit_length()-1
                if pivot in pivots:
                    value ^= pivots[pivot]
                else:
                    pivots[pivot] = value
                    break
        assert len(pivots) == expected
        results.append(dict(connected=connected,native_equations=len(cnf.native_xors),
                            coefficient_rank_GF2=len(pivots),variables=cnf.variables,
                            ordinary_clauses=len(cnf.clauses)))
    (ROOT/'experiments/exact_parity_linear_structure.json').write_text(json.dumps(results,indent=2)+'\n')
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix',action='store_true')
    parser.add_argument('--seconds',type=float,default=90)
    args = parser.parse_args()
    gates = gate_checks()
    linear_structure()
    certificate = json.loads((ROOT/'sources/anc/certificates.json').read_text())
    bad = json.loads((ROOT/'experiments/exact_structure_counterexample.json').read_text())['rows']
    cases = []
    for layout,connected in [('chain',False),('tree',False),('chain',True)]:
        for orbit in (False,True):
            cases.append(('binary',2,[],orbit,layout,connected,42 if orbit else 168))
    for connected in (False,True):
        cases += [('ternary_fixed',3,certificate['ternary_seeds'][0],False,'chain',connected,1),
                  ('ternary_invalid',3,bad,False,'chain',connected,0)]
    if args.prefix:
        for connected in (False,True):
            cases.append(('prefix_C',3,certificate['ternary_prefixes']['C'],False,'chain',connected,2))
    records = []
    with tempfile.TemporaryDirectory(prefix='exact_parity_check_') as directory:
        path = Path(directory)/'case.cnf'
        for label,colors,prefix,orbit,layout,connected,expected in cases:
            cnf,cells,stats = make_parity_cnf(colors,prefix,orbit_canonical=orbit,
                                              layout=layout,connected=connected)
            # All nontrivial solved cases use a verified all-false witness.
            if label in ('binary','prefix_C'):
                seed = 1 if label == 'prefix_C' else 0
                board = normalize_board(default_board(colors,seed),colors,'orbit' if orbit else 'none')
                assert board[:len(prefix)] == prefix
                cnf = rephase_parity(cnf,cells,board)
            write_parity(path,cnf,cells)
            started = time.monotonic()
            try:
                count = exact_count(path,args.seconds)
                assert count == expected,(label,layout,connected,orbit,count,expected)
                status = 'complete'
            except subprocess.TimeoutExpired:
                count = None
                status = 'timeout'
            result = dict(case=label,layout=layout,connected=connected,orbit=orbit,
                          status=status,expected=expected,exact_count=count,
                          wall_seconds=round(time.monotonic()-started,3),**stats)
            records.append(result)
            (ROOT/'experiments/exact_parity_check_results.json').write_text(json.dumps(records,indent=2)+'\n')
            print(json.dumps(result),flush=True)
    propagated = 0
    for connected in (False,True):
        cnf,cells,stats = make_parity_cnf(3,orbit_canonical=True,connected=connected)
        for board in certificate['ternary_seeds']:
            board_model(cnf,cells,normalize_board(board,3,'orbit'))
            propagated += 1
    summary = dict(functional_gate_assignments_checked=gates,
                   completed_exact_counts=sum(r['status']=='complete' for r in records),
                   timed_out_cases=sum(r['status']=='timeout' for r in records),
                   full_ternary_models_fully_propagated=propagated)
    (ROOT/'experiments/exact_parity_check_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary),flush=True)


if __name__ == '__main__':
    main()
