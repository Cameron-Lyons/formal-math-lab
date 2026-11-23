"""Optional discovery search; the Lean proof does not trust this solver."""
import argparse
import itertools
import json
from pathlib import Path

from ortools.sat.python import cp_model


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--prefix', type=int, default=6)
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--seconds', type=float, default=120)
    args = parser.parse_args()
    data = json.loads(Path('sources/anc/certificates.json').read_text())
    seeds = data['ternary_seeds']
    known = set()
    for rows in seeds:
        for perm in itertools.permutations('012'):
            for reflected in (False, True):
                known.add(tuple(int(perm[int(c)]) for row in rows
                                for c in (row[::-1] if reflected else row)))
    model = cp_model.CpModel()
    cells = [model.new_int_var(0, 2, f'c{i}') for i in range(100)]
    codes = []
    for r in range(1, 10):
        for j in range(2*r-1):
            code = model.new_int_var(0, 80, f'p{r}_{j}')
            model.add(code == 27*cells[(r-1)**2+j] + 9*cells[r*r+j]
                      + 3*cells[r*r+j+1] + cells[r*r+j+2])
            codes.append(code)
    model.add_all_different(codes)
    model.add_forbidden_assignments(cells, sorted(known))
    seed = [int(c) for row in seeds[args.seed] for c in row]
    for i, c in enumerate(seed):
        model.add_hint(cells[i], c)
        if i < args.prefix**2:
            model.add(cells[i] == c)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.seconds
    solver.parameters.num_search_workers = 3
    status = solver.solve(model)
    print(solver.response_stats(), flush=True)
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        flat = [solver.value(c) for c in cells]
        rows = [''.join(map(str, flat[r*r:(r+1)**2])) for r in range(10)]
        assert tuple(flat) not in known
        assert len({27*flat[(r-1)**2+j]+9*flat[r*r+j]+3*flat[r*r+j+1]
                    +flat[r*r+j+2] for r in range(1,10) for j in range(2*r-1)}) == 81
        Path('sat_result.json').write_text(json.dumps(rows, indent=2)+'\n')
        print('\n'.join(rows), flush=True)


if __name__ == '__main__':
    main()
