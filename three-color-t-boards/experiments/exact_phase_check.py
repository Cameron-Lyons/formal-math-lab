#!/usr/bin/env python3
"""Check rephasing by exhaustive Boolean truth tables and exact board counts."""
import itertools
import json
from pathlib import Path
import random
import re
import subprocess
import tempfile

from exact_count_cnf import CNF, make_cnf
from exact_phase import (ROOT, board_model, default_board, normalize_board,
                         propagate_model, rephase, write_cnf)


def satisfied(cnf, assignment):
    return all(any(assignment[abs(lit)] == (lit > 0) for lit in clause)
               for clause in cnf.clauses)


def main():
    rng = random.Random(20261122)
    comparisons = 0
    for size in range(1, 7):
        for _ in range(50):
            cnf = CNF()
            cnf.variables = size
            model = [None] + [bool(rng.randrange(2)) for _ in range(size)]
            for _ in range(10):
                clause = [rng.choice((-1, 1))*rng.randint(1, size)
                          for _ in range(rng.randint(1, 5))]
                if any(model[abs(lit)] == (lit > 0) for lit in clause):
                    cnf.clauses.append(clause)
            phased = rephase(cnf, model)
            assert [[-lit if model[abs(lit)] else lit for lit in clause]
                    for clause in phased.clauses] == cnf.clauses
            assert propagate_model(cnf, dict(enumerate(model[1:], start=1))) == model
            for values in itertools.product((False, True), repeat=size):
                original = [None] + list(values)
                changed = [None] + [value != model[i] for i, value in enumerate(values, start=1)]
                assert satisfied(cnf, original) == satisfied(phased, changed)
                comparisons += 1
    print(f'All {comparisons} Boolean truth-table comparisons preserve satisfaction PASS', flush=True)

    invalid = CNF()
    invalid.variables = 1
    invalid.clauses = [[1], [-1]]
    try:
        propagate_model(invalid, {})
        raise AssertionError('contradictory formula was accepted')
    except ValueError:
        pass
    print('Contradictory supplied models are rejected PASS', flush=True)

    binary = default_board(2, 0)
    ternary = json.loads((ROOT/'sources/anc/certificates.json').read_text())['ternary_seeds'][:2]
    solver = ROOT/'experiments/exact_count_tools/ganak'
    with tempfile.TemporaryDirectory(prefix='tboards-phase-check-') as directory:
        path = Path(directory)/'model.cnf'
        for amo in ('none', 'pairwise', 'binary', 'tree'):
            for normalization, expected in (('none', 168), ('palette', 84), ('orbit', 42)):
                for colors, rows in [(2, binary)] + [(3, rows) for rows in ternary]:
                    rows = normalize_board(rows, colors, normalization)
                    cnf, cells = make_cnf(colors, [], normalization != 'none', amo,
                                          normalization == 'orbit')
                    model = board_model(cnf, cells, rows)
                    phased = rephase(cnf, model)
                    assert [[-lit if model[abs(lit)] else lit for lit in clause]
                            for clause in phased.clauses] == cnf.clauses
                    assert satisfied(phased, [None] + [False]*cnf.variables)
                    if colors != 2:
                        continue
                    # Count all Boolean variables, with no projection hint.
                    write_cnf(path, phased)
                    result = subprocess.run([str(solver), '--prob', '0', '--arjun', '0',
                                             '--puura', '0', '--td', '0', '--maxcache', '256',
                                             str(path)], capture_output=True, text=True, timeout=15)
                    found = re.search(r'^c s exact arb int (\d+)$', result.stdout, re.M)
                    assert result.returncode == 0 and found, result.stdout[-2000:]
                    assert int(found[1]) == expected
                    print(f'binary {normalization} {amo}: exact phased count={expected} PASS', flush=True)
    print('All 36 complete board models propagated and rephased bijectively PASS', flush=True)


if __name__ == '__main__':
    main()
