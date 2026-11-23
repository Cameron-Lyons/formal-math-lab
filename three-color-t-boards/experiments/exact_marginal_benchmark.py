#!/usr/bin/env python3
"""Bound exact-counter runs and retain explicit timeout/progress metadata."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]


def benchmark(path, seconds):
    log = ROOT/'experiments'/('exact_marginal_bench_'+path.stem+'.log')
    command = ['timeout', '--kill-after=2s', str(seconds),
               str(ROOT/'experiments/exact_count_tools/ganak'),
               '--prob', '0', '--arjun', '0', '--puura', '0', '--td', '0',
               '--maxcache', '512', str(path.resolve())]
    started = time.monotonic()
    with log.open('w') as output:
        process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        # wait4 gives per-process CPU and memory usage, including the solver
        # child reaped by timeout, without mixing concurrent benchmark runs.
        _, status, usage = os.wait4(process.pid, 0)
        code = os.waitstatus_to_exitcode(status)
        process.returncode = code
    wall = time.monotonic()-started
    text = log.read_text()
    count = re.search(r'^c s exact arb int (\d+)$', text, re.M)
    conflicts = re.findall(r'^c o conflicts\s+(\d+)', text, re.M)
    decisions = re.findall(r'^c o decisions K\s+(\d+)', text, re.M)
    rdb = re.findall(r'rdb: (\d+)', text)
    result = {'cnf': str(path), 'log': str(log.relative_to(ROOT)), 'command': command,
              'status': 'complete' if code == 0 and count else ('timeout' if code in (124, 137, -9) else 'failed'),
              'exact_count': int(count[1]) if code == 0 and count else None,
              'exit_code': code, 'wall_seconds': round(wall, 3), 'limit_wall_seconds': seconds,
              'user_seconds': round(usage.ru_utime, 3),
              'system_seconds': round(usage.ru_stime, 3),
              'max_rss_kb': usage.ru_maxrss,
              'last_reported_conflicts': int(conflicts[-1]) if conflicts else None,
              'last_reported_decisions_thousands': int(decisions[-1]) if decisions else None,
              'last_reported_clause_database_reduction': int(rdb[-1]) if rdb else None,
              'passed_initial_sat': bool('[bce]' in text or rdb or count),
              'counting_search_observed': bool(rdb or conflicts or count)}
    print(json.dumps(result), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=int, default=60)
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('cnfs', nargs='+', type=Path)
    args = parser.parse_args()
    if args.seconds < 1 or args.jobs < 1:
        parser.error('seconds and jobs must be positive')
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda path: benchmark(path, args.seconds), args.cnfs))
    args.output.write_text(json.dumps(results, indent=2)+'\n')


if __name__ == '__main__':
    main()
