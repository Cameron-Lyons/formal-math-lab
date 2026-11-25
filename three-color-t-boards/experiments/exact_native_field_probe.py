#!/usr/bin/env python3
"""Independent exact counting probes with the whole prime field as palette.

These are a full binary validation and a fixed ternary prefix, not an
unrestricted ternary count. In F_q the only nonzero target power moment
has every exponent q-1, and its value is one (there are four roles).
"""
from collections import defaultdict
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import time

from exact_algebra_backend import monomial_dimension
from exact_msolve_backend import parse_leading, poly_text
from exact_standard_monomials import count_standard_monomials

HERE = Path(__file__).resolve().parent
SIX_PREFIX = '100011101011000101010011112112211212021201221022121202020220010222002102100022222'


def model(q, prefix=''):
    height = q*q+1
    cells = [(r, c) for r in range(height) for c in range(-r, r+1)]
    index = {cell:i for i,cell in enumerate(cells)}
    patterns = [(index[r-1,c], index[r,c-1], index[r,c], index[r,c+1])
                for r in range(1, height) for c in range(1-r, r)]
    assert len(patterns) == q**4
    n = len(cells)-len(prefix)
    equations = [f'x{i+1}^{q}+{q-1}*x{i+1}' for i in range(n)]
    labels = [f'domain:{i+len(prefix)}' for i in range(n)]
    for exponents in itertools.product(range(q), repeat=4):
        if not any(exponents):
            continue
        coefficients = defaultdict(int)
        for pattern in patterns:
            powers = [0]*n
            coefficient = 1
            for cell, exponent in zip(pattern, exponents):
                if cell < len(prefix):
                    coefficient = coefficient*pow(int(prefix[cell]), exponent, q) % q
                else:
                    powers[cell-len(prefix)] += exponent
            coefficients[tuple(powers)] += coefficient
        if exponents == (q-1,)*4:
            coefficients[(0,)*n] -= 1
        equations.append(poly_text(coefficients, q))
        labels.append('moment:'+','.join(map(str, exponents)))
    return ','.join(f'x{i+1}' for i in range(n))+'\n'+str(q)+'\n'+',\n'.join(equations)+'\n', n, labels


def main():
    directory = HERE/'exact_native_field_probe_runs'
    directory.mkdir(exist_ok=False)
    executable = HERE/'exact_msolve_f2_bitset_tools/msolve'
    env = dict(os.environ, LD_LIBRARY_PATH=str(HERE/'exact_algebra_backend_root/usr/lib'))

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (2*1024**3,)*2)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    results = []
    for name, q, prefix, expected in [('binary_full', 2, '', 168), ('ternary_six', 3, SIX_PREFIX, 6)]:
        source, n, labels = model(q, prefix)
        input_path, basis_path = directory/(name+'.ms'), directory/(name+'.basis')
        input_path.write_text(source)
        command = [str(executable.resolve()), '-g', '1', '-l', '2', '-t', '1', '-r', '1',
                   '-c', '0', '-v', '2', '-m', '16', '-f', str(input_path), '-o', str(basis_path)]
        record = dict(name=name, prime=q, variables=n, generators=len(labels), prefix=prefix,
                      scope='all binary boards' if q==2 else 'fixed ternary prefix completions',
                      count_divisor=1, count_multiplier=1, command=command,
                      input_sha256=hashlib.sha256(source.encode()).hexdigest(),
                      expected_count_decimal=str(expected), status='INCOMPLETE')
        started = time.monotonic()
        with (directory/(name+'.log')).open('x') as log_file:
            try:
                process = subprocess.run(command, stdout=log_file, stderr=subprocess.STDOUT,
                                         timeout=30, preexec_fn=limits, env=env)
                record['returncode'] = process.returncode
            except subprocess.TimeoutExpired:
                record['status'] = 'INCOMPLETE_TIMEOUT'
        record['elapsed_seconds'] = time.monotonic()-started
        log = (directory/(name+'.log')).read_text()
        record['export_marker_count'] = log.splitlines().count('MSOLVE_PRIME_GB_EXPORT_COMPLETE')
        record['error_diagnostics'] = [line for line in log.splitlines()
            if re.search(r'error|out of memory|cannot allocate|segmentation|aborted', line, re.I)]
        if record.get('returncode') == 0 and record['export_marker_count'] == 1 and not record['error_diagnostics']:
            leading = parse_leading(basis_path.read_text(), n, q)
            first, _ = monomial_dimension(leading, n, seconds=10)
            second = count_standard_monomials(leading, n, standard_basis_complete=True)
            assert first == second == expected, (name, first, second)
            record.update(status='COMPLETE_VERIFIED', dimension_decimal=str(first),
                          independent_count_decimal=str(second), board_count_decimal=str(first),
                          basis_sha256=hashlib.sha256(basis_path.read_bytes()).hexdigest(),
                          leading_monomials=len(leading))
        results.append(record)
        print(json.dumps(record), flush=True)
    (HERE/'exact_native_field_probe_results.json').write_text(json.dumps(dict(
        results=results, unrestricted_ternary_count_computed=False,
        executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest()), indent=2)+'\n')


if __name__ == '__main__':
    main()
