#!/usr/bin/env python3
"""Compare deterministic counting polarities on the witnessed, rephased CNF."""
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
EXPERIMENTS = ROOT/'experiments'


def check_all_false(path):
    current = []
    for line in path.read_text().splitlines():
        if not line or line[0] in 'cp':
            continue
        for token in line.split():
            literal = int(token)
            if literal:
                current.append(literal)
            else:
                if not any(x < 0 for x in current):
                    raise ValueError('input CNF does not admit the all-false model')
                current = []
    if current:
        raise ValueError('unterminated DIMACS clause')


def run(scope, polarity, seconds):
    cnf = EXPERIMENTS/f'exact_phase_{scope}.cnf'
    check_all_false(cnf)
    log = EXPERIMENTS/f'exact_phase_polar_{scope}_{polarity}.log'
    command = ['timeout', '--kill-after=2s', str(seconds),
               str(EXPERIMENTS/'exact_count_tools/ganak'), '--prob', '0',
               '--arjun', '0', '--puura', '0', '--td', '0', '--maxcache', '512',
               '--polar', str(polarity), '--verb', '2', str(cnf)]
    started = time.monotonic()
    with log.open('w') as output:
        process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        _, status, usage = os.wait4(process.pid, 0)
        code = os.waitstatus_to_exitcode(status)
        process.returncode = code
    text = log.read_text()
    match = re.search(r'^c s exact arb int (\d+)$', text, re.M)
    conflicts = re.findall(r'^c o conflicts\s+(\d+)', text, re.M)
    decisions = re.findall(r'^c o decisions K\s+(\d+)', text, re.M)
    rdb = re.findall(r'rdb: (\d+)', text)
    result = {'scope': scope, 'polarity': polarity, 'command': command,
              'cnf_sha256': hashlib.sha256(cnf.read_bytes()).hexdigest(),
              'status': 'complete' if code == 0 and match else ('timeout' if code in (124, 137, -9) else 'failed'),
              'exact_count': int(match[1]) if code == 0 and match else None,
              'exit_code': code, 'wall_seconds': round(time.monotonic()-started, 3),
              'limit_wall_seconds': seconds, 'user_seconds': round(usage.ru_utime, 3),
              'system_seconds': round(usage.ru_stime, 3), 'max_rss_kb': usage.ru_maxrss,
              'passed_initial_sat': bool('[bce]' in text or rdb or match),
              'counting_search_observed': bool(rdb or conflicts or match),
              'last_reported_conflicts': int(conflicts[-1]) if conflicts else None,
              'last_reported_decisions_thousands': int(decisions[-1]) if decisions else None,
              'last_reported_clause_database_reduction': int(rdb[-1]) if rdb else None,
              'log': str(log.relative_to(ROOT))}
    print(json.dumps(result), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=int, default=120)
    parser.add_argument('--binary-only', action='store_true')
    args = parser.parse_args()
    if args.seconds < 1:
        parser.error('seconds must be positive')
    results = []
    for polarity in (1, 3):
        result = run('binary', polarity, 30)
        if result['exact_count'] != 42:
            raise AssertionError(result)
        results.append(result)
    if not args.binary_only:
        with ThreadPoolExecutor(max_workers=2) as pool:
            results.extend(pool.map(lambda p: run('ternary', p, args.seconds), (1, 3)))
    (EXPERIMENTS/'exact_phase_polar_results.json').write_text(json.dumps(results, indent=2)+'\n')


if __name__ == '__main__':
    main()
