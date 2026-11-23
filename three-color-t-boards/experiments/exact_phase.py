#!/usr/bin/env python3
"""Rephase a count-preserving board CNF so a known model is all false.

This changes no model count and fixes no board cells. Each Boolean variable
is independently complemented when its value in the supplied model is true.
The map is a bijection between all models of the original and rephased CNFs.
"""
from collections import deque
import argparse
import itertools
import json
from pathlib import Path
import sys

from exact_count_cnf import CNF, make_cnf

ROOT = Path(__file__).resolve().parents[1]


def normalize_board(rows, colors, mode):
    if mode == 'none':
        return rows
    images = []
    for permutation in itertools.permutations(range(colors)):
        for reflected in ((False, True) if mode == 'orbit' else (False,)):
            images.append([''.join(str(permutation[int(c)]) for c in
                                   (row[::-1] if reflected else row)) for row in rows])
    return min(images)


def propagate_model(cnf, initial):
    """Determine functional auxiliaries by ordinary Boolean unit propagation.

    Reject contradictions or incomplete propagation, then independently
    evaluate every original clause on the resulting complete assignment.
    """
    assignment = [None] * (cnf.variables + 1)
    occurrences = [[] for _ in assignment]
    remaining, xors, satisfied = [], [], []
    queue = deque(initial.items())
    for clause in cnf.clauses:
        unique = set(clause)
        if any(-literal in unique for literal in unique):
            continue
        if not unique:
            raise ValueError('empty clause: supplied model cannot satisfy this CNF')
        index = len(remaining)
        remaining.append(len(unique))
        value = 0
        for literal in unique:
            if not 1 <= abs(literal) <= cnf.variables:
                raise ValueError('CNF literal outside declared variable range')
            value ^= literal
            occurrences[abs(literal)].append((index, literal))
        xors.append(value)
        satisfied.append(False)
        if len(unique) == 1:
            literal = next(iter(unique))
            queue.append((abs(literal), literal > 0))
    while queue:
        variable, value = queue.popleft()
        if not 1 <= variable <= cnf.variables:
            raise ValueError('initial assignment outside declared variable range')
        value = bool(value)
        if assignment[variable] is not None:
            if assignment[variable] != value:
                raise ValueError('supplied model contradicts the CNF')
            continue
        assignment[variable] = value
        for index, literal in occurrences[variable]:
            if satisfied[index]:
                continue
            if value == (literal > 0):
                satisfied[index] = True
                continue
            remaining[index] -= 1
            xors[index] ^= literal
            if remaining[index] == 0:
                raise ValueError('supplied model falsifies a clause')
            if remaining[index] == 1:
                unit = xors[index]
                queue.append((abs(unit), unit > 0))
    missing = [v for v in range(1, len(assignment)) if assignment[v] is None]
    if missing:
        raise ValueError(f'unit propagation left {len(missing)} auxiliary variables undetermined')
    if not all(any(assignment[abs(lit)] == (lit > 0) for lit in clause)
               for clause in cnf.clauses):
        raise AssertionError('complete model failed independent clause evaluation')
    return assignment


def rephase(cnf, assignment):
    if len(assignment) != cnf.variables + 1 or any(v is None for v in assignment[1:]):
        raise ValueError('a complete one-indexed model is required')
    result = CNF()
    result.variables = cnf.variables
    result.clauses = [[-literal if assignment[abs(literal)] else literal
                       for literal in clause] for clause in cnf.clauses]
    if not all(any(lit < 0 for lit in clause) for clause in result.clauses):
        raise ValueError('rephased CNF does not accept the all-false assignment')
    return result


def board_model(cnf, cells, rows):
    flat = [int(c) for row in rows for c in row]
    return propagate_model(cnf, {variable: flat[pos] == color
                                for pos, indicators in cells.items()
                                for color, variable in enumerate(indicators)})


def write_cnf(path, cnf, cells=None):
    with Path(path).open('w') as file:
        file.write('c Independent variable complements preserve the exact model count.\n')
        file.write('c A verified complete board model is the all-false assignment.\n')
        if cells is not None:
            support = [v for indicators in cells.values() for v in indicators[:-1]]
            file.write('c ind ' + ' '.join(map(str, support)) + ' 0\n')
        file.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for clause in cnf.clauses:
            file.write(' '.join(map(str, clause)) + ' 0\n')


def default_board(colors, seed):
    if colors == 3:
        data = json.loads((ROOT/'sources/anc/certificates.json').read_text())
        return data['ternary_seeds'][seed]
    if colors == 1:
        return ['0', '000']
    sys.path.insert(0, str(ROOT/'sources/anc'))
    from count_extensions import count_extensions
    board = count_extensions(2, [])[0][seed]
    return [''.join(map(str, board[r*r:(r+1)**2])) for r in range(5)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--colors', type=int, choices=(1, 2, 3), default=3)
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--normalize', choices=('none', 'palette', 'orbit'), default='orbit')
    parser.add_argument('--prefix-rows', type=int, default=0)
    parser.add_argument('--occurrence-amo', choices=('none', 'pairwise', 'binary', 'tree'), default='tree')
    parser.add_argument('--no-support', action='store_true')
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    if not 0 <= args.prefix_rows <= args.colors**2+1:
        parser.error('--prefix-rows must lie within the board')
    if args.prefix_rows and args.normalize != 'none':
        parser.error('a fixed prefix requires --normalize none')
    board = normalize_board(default_board(args.colors, args.seed), args.colors, args.normalize)
    prefix = board[:args.prefix_rows]
    cnf, cells = make_cnf(args.colors, prefix, args.normalize != 'none',
                         args.occurrence_amo, args.normalize == 'orbit')
    assignment = board_model(cnf, cells, board)
    phased = rephase(cnf, assignment)
    write_cnf(args.output, phased, None if args.no_support else cells)
    metadata = dict(colors=args.colors, prefix=prefix, normalization=args.normalize,
                    occurrence_amo=args.occurrence_amo,
                    independent_support=not args.no_support,
                    variables=cnf.variables, clauses=len(cnf.clauses),
                    complemented=sum(assignment[1:]), board=board,
                    all_false_verified=True, count_preserved=True,
                    full_count_computed=False)
    Path(str(args.output)+'.json').write_text(json.dumps(metadata, indent=2)+'\n')
    print(json.dumps(metadata))


if __name__ == '__main__':
    main()
