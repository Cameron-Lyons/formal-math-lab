#!/usr/bin/env python3
"""Validate the independent d4 engine, then run at most two bounded full trials.

All counts use GMP integers and all CNF variables. A timeout has no count.
The input encoders and witness rephasing are imported without modification.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

from exact_count_cnf import make_cnf
from exact_phase import board_model, default_board, normalize_board, rephase, write_cnf

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'experiments'
SOLVER = OUT / 'exact_backend_tools/d4/d4'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def prepare():
    cases = []
    for name, colors, mode, fixed_rows, seed, expected in [
        ('binary_raw', 2, 'none', 0, 0, 168),
        ('binary_orbit', 2, 'orbit', 0, 0, 42),
        ('ternary_fixed', 3, 'none', 0, 0, 1),
        ('prefix_C', 3, 'none', 7, 1, 2),
    ]:
        board = normalize_board(default_board(colors, seed), colors, mode)
        prefix = board[:fixed_rows]
        cnf, cells = make_cnf(colors, prefix, mode != 'none', 'tree', mode == 'orbit')
        if name == 'ternary_fixed':
            flat = [int(c) for row in board for c in row]
            for pos, indicators in cells.items():
                cnf.add([indicators[flat[pos]]])
        assignment = board_model(cnf, cells, board)
        path = OUT / f'exact_backend_{name}.cnf'
        write_cnf(path, rephase(cnf, assignment))
        cases.append((name, path, expected))
    return cases


def run(name, path, seconds, expected=None):
    log = OUT / f'exact_backend_{name}.log'
    command = ['timeout', '--kill-after=2s', str(seconds), 'stdbuf', '-oL', '-eL',
               str(SOLVER), str(path.resolve()), '-mc', '-ph=TRUE', '-rnd-seed=91648253']
    started = time.monotonic()
    with log.open('w') as output:
        process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        _, status, usage = os.wait4(process.pid, 0)
        code = os.waitstatus_to_exitcode(status)
        process.returncode = code
    contents = log.read_text()
    count = re.search(r'^s (\d+)$', contents, re.M)
    exact = int(count[1]) if code == 0 and count else None
    integer_mode = 'c Integer mode' in contents
    if exact is not None and not integer_mode:
        raise AssertionError('d4 did not confirm its exact integer arithmetic mode')
    traces = []
    for line in contents.splitlines():
        if line.startswith('c exact_backend_trace '):
            traces.append({('solver_elapsed_seconds' if key == 'cpu' else key):
                           float(value) if key == 'cpu' else int(value)
                           for key, value in re.findall(r'(\w+)=(-?[\d.]+)', line)})
    periodic = []
    for line in contents.splitlines():
        if re.match(r'^c\s+\d+\s+\|', line):
            values = [v.strip() for v in line[1:].split('|') if v.strip()]
            if len(values) == 10:
                periodic.append(dict(zip(['calls', 'solver_elapsed_seconds', 'cache_hits', 'cache_misses',
                                          'split_components', 'solver_virtual_peak_mb', 'equiv_calls',
                                          'decisions', 'partition_calls', 'cache_limit'],
                                         [float(x) if i == 1 else int(x)
                                          for i, x in enumerate(values)])))
    final_stats = {}
    for key, label in [('calls', 'recursive call'), ('split_components', 'split formula'),
                       ('decisions', 'decision'), ('partition_calls', 'paritioner calls'),
                       ('cache_hits', 'positive hit'), ('cache_misses', 'negative hit')]:
        matches = re.findall(r'^c Number of ' + label + r': (\d+)$', contents, re.M)
        if matches:
            final_stats[key] = int(matches[-1])
    result = dict(name=name, input=str(path.relative_to(ROOT)), input_sha256=digest(path),
                  solver_sha256=digest(SOLVER), command=command, log=str(log.relative_to(ROOT)),
                  status='complete' if exact is not None else
                  ('timeout' if code in (124, 137, -9) else 'failed'),
                  exit_code=code, exact_count=exact, expected_count=expected,
                  expected_count_verified=(exact == expected) if expected is not None else None,
                  integer_mode=integer_mode, counting_all_variables=True,
                  limit_wall_seconds=seconds, wall_seconds=round(time.monotonic()-started, 3),
                  user_seconds=round(usage.ru_utime, 3), system_seconds=round(usage.ru_stime, 3),
                  cpu_seconds=round(usage.ru_utime + usage.ru_stime, 3),
                  max_rss_kb=usage.ru_maxrss, decision_traces=traces,
                  last_periodic_stats=periodic[-1] if periodic else None,
                  final_stats=final_stats,
                  counter_search_observed=bool(traces or periodic or final_stats))
    print(json.dumps({k:v for k,v in result.items() if k != 'decision_traces'}), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true', help='Run the two full trials after validation.')
    parser.add_argument('--seconds', type=int, default=120)
    args = parser.parse_args()
    if not 1 <= args.seconds <= 120:
        parser.error('each wall limit must lie between 1 and 120 seconds')
    if not SOLVER.is_file():
        parser.error('build the pinned d4 source as described in exact_backend_notes.md')
    records = []
    output = OUT / 'exact_backend_results.json'
    for name, path, expected in prepare():
        records.append(run(name, path, args.seconds if name == 'prefix_C' else 30, expected))
        output.write_text(json.dumps(records, indent=2) + '\n')
        if records[-1]['exact_count'] is not None and records[-1]['exact_count'] != expected:
            raise AssertionError(f'{name}: independent counter disagrees with the known exact count')
    if args.full and all(r['expected_count_verified'] for r in records):
        for name, file in [('full_baseline', 'exact_phase_ternary.cnf'),
                           ('full_compare', 'exact_compare_ternary.cnf')]:
            records.append(run(name, OUT / file, args.seconds))
            output.write_text(json.dumps(records, indent=2) + '\n')
    elif args.full:
        print('Full trials skipped: validation did not complete successfully.', flush=True)


if __name__ == '__main__':
    main()
