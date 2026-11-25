#!/usr/bin/env python3
"""Bounded solver checks of ordinary F4 prefix sums, with exact known counts."""
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import time

from exact_algebra_backend import monomial_dimension
from exact_msolve_backend import parse_leading
from exact_standard_monomials import count_standard_monomials

HERE = Path(__file__).resolve().parent


def main():
    directory = HERE / 'exact_prefix_chain_probe_runs'
    directory.mkdir(exist_ok=False)
    executable = HERE / 'exact_msolve_f2_bitset_tools/msolve'
    env = dict(os.environ, LD_LIBRARY_PATH=str(HERE/'exact_algebra_backend_root/usr/lib'))
    reports = []

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (2*1024**3,)*2)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    for length in (12, 30):
        # z_i = y_i + y_(i-1), y_(-1)=y_(length-1)=0.
        # Every z_i is a nonzero F4 element; the total sum is zero.
        variables = length-1
        domains = ['x1^3+1']
        for i in range(2, length):
            a, b = f'x{i}', f'x{i-1}'
            domains.append(f'{a}^3+{a}^2*{b}+{a}*{b}^2+{b}^3+1')
        domains.append(f'x{variables}^3+1')
        expected = (3**length+3*(-1)**length)//4
        for fields in (False, True):
            name = f'length{length}_fields{int(fields)}'
            equations = domains + ([f'x{i}^4+x{i}' for i in range(1, length)] if fields else [])
            source = ','.join(f'x{i}' for i in range(1, length))+'\n2\n'+',\n'.join(equations)+'\n'
            input_path, basis_path = directory/(name+'.ms'), directory/(name+'.basis')
            input_path.write_text(source)
            command = [str(executable.resolve()), '-g', '1', '-l', '2', '-t', '1',
                       '-r', '1', '-c', '0', '-v', '2', '-m', '16',
                       '-f', str(input_path), '-o', str(basis_path)]
            started = time.monotonic()
            record = dict(length=length, variables=variables, field_equations=fields,
                          command=command, expected_dimension_decimal=str(expected),
                          input_sha256=hashlib.sha256(source.encode()).hexdigest(),
                          status='INCOMPLETE', wall_limit_seconds=12, memory_mb=2048)
            with (directory/(name+'.log')).open('x') as log_file:
                try:
                    child = subprocess.run(command, stdout=log_file, stderr=subprocess.STDOUT,
                                           timeout=12, env=env, preexec_fn=limits)
                    record['returncode'] = child.returncode
                except subprocess.TimeoutExpired:
                    record['status'] = 'INCOMPLETE_TIMEOUT'
            record['elapsed_seconds'] = time.monotonic()-started
            log = (directory/(name+'.log')).read_text()
            record['export_marker_count'] = log.splitlines().count('MSOLVE_PRIME_GB_EXPORT_COMPLETE')
            record['error_diagnostics'] = [line for line in log.splitlines()
                if re.search(r'error|out of memory|cannot allocate|segmentation|aborted', line, re.I)]
            if (record.get('returncode') == 0 and record['export_marker_count'] == 1
                    and not record['error_diagnostics']):
                leading = parse_leading(basis_path.read_text(), variables, 2)
                first, _ = monomial_dimension(leading, variables, seconds=10)
                second = count_standard_monomials(leading, variables, standard_basis_complete=True)
                assert first == second == expected, (name, first, second, expected)
                record.update(status='COMPLETE_VERIFIED_FIXTURE', dimension_decimal=str(first),
                              leading_monomials=len(leading),
                              basis_sha256=hashlib.sha256(basis_path.read_bytes()).hexdigest())
            reports.append(record)
            print(json.dumps(record), flush=True)
    report = dict(scope='prefix-chain domain fixtures; no T-board count',
                  executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest(), results=reports)
    (HERE/'exact_prefix_chain_probe_results.json').write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
