#!/usr/bin/env python3
"""Independently compare small complete bases for retained-column promotion.

The reference is a small exact Python Buchberger implementation. This script
runs no T-board instance and keeps each external arithmetic fixture bounded.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import time

from exact_msolve_review import parse_polynomial

ROOT = Path(__file__).resolve().parents[1]


def monomial_key(exponents):
    return sum(exponents), tuple(-x for x in reversed(exponents))


def leading(polynomial):
    return max(polynomial, key=monomial_key)


def monic(polynomial, prime):
    if not polynomial:
        return {}
    inverse = pow(polynomial[leading(polynomial)], -1, prime)
    return {key: value*inverse % prime for key, value in polynomial.items()}


def divides(divisor, monomial):
    return all(a <= b for a, b in zip(divisor, monomial))


def reduce_polynomial(polynomial, basis, prime):
    pending = dict(polynomial)
    remainder = {}
    while pending:
        term = leading(pending)
        for reducer in basis:
            pivot = leading(reducer)
            if divides(pivot, term):
                multiplier = tuple(a-b for a, b in zip(term, pivot))
                scalar = pending[term]*pow(reducer[pivot], -1, prime) % prime
                for exponents, coefficient in reducer.items():
                    destination = tuple(a+b for a, b in zip(exponents, multiplier))
                    value = (pending.get(destination, 0)-scalar*coefficient) % prime
                    if value:
                        pending[destination] = value
                    else:
                        pending.pop(destination, None)
                break
        else:
            remainder[term] = pending.pop(term)
    return remainder


def buchberger(generators, prime):
    basis = []
    for generator in generators:
        reduced = reduce_polynomial(generator, basis, prime)
        if reduced:
            basis.append(monic(reduced, prime))
    pairs = list(itertools.combinations(range(len(basis)), 2))
    cursor = 0
    while cursor < len(pairs):
        assert len(basis) < 500 and cursor < 100000, 'tiny reference fixture too large'
        left, right = (basis[index] for index in pairs[cursor]); cursor += 1
        lm_left, lm_right = leading(left), leading(right)
        if all(not(a and b) for a, b in zip(lm_left, lm_right)):
            continue  # Relatively prime leading monomials: product criterion.
        common = tuple(max(a, b) for a, b in zip(lm_left, lm_right))
        s_polynomial = {}
        for sign, polynomial, pivot in ((1, left, lm_left), (-1, right, lm_right)):
            multiplier = tuple(a-b for a, b in zip(common, pivot))
            for exponents, coefficient in polynomial.items():
                destination = tuple(a+b for a, b in zip(exponents, multiplier))
                value = (s_polynomial.get(destination, 0)+sign*coefficient) % prime
                if value:
                    s_polynomial[destination] = value
                else:
                    s_polynomial.pop(destination, None)
        reduced = reduce_polynomial(s_polynomial, basis, prime)
        if reduced:
            pairs.extend((i, len(basis)) for i in range(len(basis)))
            basis.append(monic(reduced, prime))
    minimal = []
    for polynomial in sorted(basis, key=lambda item: monomial_key(leading(item))):
        if not any(divides(leading(other), leading(polynomial)) for other in minimal):
            minimal.append(polynomial)
    result = [monic(reduce_polynomial(polynomial, minimal[:i]+minimal[i+1:], prime), prime)
              for i, polynomial in enumerate(minimal)]
    assert all(result)
    return sorted(result, key=lambda item: monomial_key(leading(item)))


def parse_full_basis(text, variables, prime):
    assert text.splitlines().count('#Reduced Groebner basis data') == 1
    assert re.search(r'#field characteristic:\s*'+str(prime)+r'\s*$', text, re.M)
    assert re.search(r'#monomial order:\s*graded reverse lexicographical\s*$', text, re.M)
    order = re.search(r'#variable order:\s*([^\n]+)', text)
    assert order and [part.strip() for part in order[1].split(',')] == [f'x{i+1}' for i in range(variables)]
    size = int(re.search(r'#length of basis:\s*(\d+)', text)[1])
    payload = '\n'.join(line for line in text.splitlines() if not line.startswith('#'))
    match = re.fullmatch(r'\s*\[(.*)\]:\s*', payload, re.S)
    assert match
    polynomials = [parse_polynomial(part.strip(), variables, prime)
                   for part in match[1].split(',')]
    assert len(polynomials) == size and all(polynomials)
    return sorted(polynomials, key=lambda item: monomial_key(leading(item)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, default=ROOT/'experiments/exact_msolve_patched_tools/msolve')
    parser.add_argument('--candidate', type=Path, default=ROOT/'experiments/exact_msolve_sparse_promotion_tools/msolve')
    parser.add_argument('--artifact-prefix', default='exact_msolve_sparse_review')
    parser.add_argument('--initial-hash-log2', type=int)
    args = parser.parse_args()
    assert re.fullmatch(r'exact_msolve_[a-z_]+', args.artifact_prefix)
    result_dir = ROOT/'experiments'/(args.artifact_prefix+'_runs')
    result_dir.mkdir(exist_ok=True)
    local_lib = ROOT/'experiments/exact_algebra_backend_root/usr/lib'
    env = dict(os.environ, LD_LIBRARY_PATH=str(local_lib))
    results = []
    fixtures = [
        ('root-sum', 3, ['x1^3-1', 'x2^3-1', 'x3^3-1', 'x1+x2+x3']),
        ('root-product', 3, ['x1^3-1', 'x2^3-1', 'x3^3-1', 'x1*x2*x3-1']),
        ('mixed', 2, ['x1^3-1', 'x2^3-1', 'x1*x2-1']),
        ('cycle', 3, ['x1^2-x2', 'x2^2-x3', 'x3^2-x1']),
        ('mixed-chain', 4, ['x1^3-1', 'x2^3-1', 'x3^3-1', 'x4^3-1',
                            'x1*x2-x3', 'x2*x3-x4']),
    ]
    for prime in (2, 5, 29, 257, 65537):
        for name, variables, equations in fixtures:
            stem = f'{name}_{prime}'
            input_path = result_dir/(stem+'.ms')
            input_path.write_text(','.join(f'x{i+1}' for i in range(variables))+'\n'+str(prime)+'\n'+',\n'.join(equations)+'\n')
            parsed_input = [parse_polynomial(equation, variables, prime) for equation in equations]
            reference_started = time.monotonic()
            reference = buchberger(parsed_input, prime)
            reference_seconds = time.monotonic()-reference_started
            assert all(not reduce_polynomial(equation, reference, prime) for equation in parsed_input)
            runs = []
            exports = []
            for kind, executable in (('baseline', args.baseline), ('candidate', args.candidate)):
                output_path = result_dir/(stem+'_'+kind+'.basis')
                if output_path.exists():
                    output_path.unlink()  # Only this review's reproducible fixture artifacts.
                command = [str(executable.resolve()), '-g', '2', '-l', '2', '-t', '1',
                           '-r', '1', '-c', '0', '-v', '2', '-f', str(input_path), '-o', str(output_path)]
                if args.initial_hash_log2 is not None:
                    command += ['-s', str(args.initial_hash_log2)]
                def limits():
                    resource.setrlimit(resource.RLIMIT_AS, (2048*1024**2,)*2)
                    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
                completed = subprocess.run(command, capture_output=True, text=True,
                                           timeout=10, env=env, preexec_fn=limits)
                log = completed.stdout+completed.stderr
                (result_dir/(stem+'_'+kind+'.log')).write_text(log)
                assert completed.returncode == 0, (stem, kind, completed.returncode, log)
                assert log.splitlines().count('MSOLVE_PRIME_GB_EXPORT_COMPLETE') == 1
                assert not re.search(r'\berror\b|segmentation|out of memory|aborted', log, re.I)
                export = output_path.read_text()
                actual = parse_full_basis(export, variables, prime)
                assert actual == reference, (stem, kind, actual, reference)
                exports.append(export)
                runs.append(dict(kind=kind, command=command,
                                 export_sha256=hashlib.sha256(export.encode()).hexdigest(),
                                 promotion_lines=[line for line in log.splitlines()
                                                  if 'promot' in line.lower()]))
            assert exports[0] == exports[1], stem
            results.append(dict(fixture=stem, prime=prime, variables=variables,
                                independent_basis_size=len(reference),
                                independent_reference_seconds=reference_seconds,
                                byte_identical=True, both_match_independent_buchberger=True, runs=runs))
    selective_rounds = []
    for result in results:
        for run in result['runs']:
            if run['kind'] == 'candidate':
                for line in run['promotion_lines']:
                    match = re.search(r'nonpivot=(\d+) referenced=(\d+) inserted=(\d+)', line)
                    if match and int(match[1]) > int(match[2]):
                        selective_rounds.append(dict(fixture=result['fixture'],
                                                     nonpivot=int(match[1]), referenced=int(match[2])))
    assert {entry['fixture'].split('_')[-1] for entry in selective_rounds} == {'2', '5', '29', '257', '65537'}
    report = dict(status='PASS', complete_basis_comparisons=len(results),
                  actual_unused_column_skipping_rounds=selective_rounds,
                  initial_hash_log2=args.initial_hash_log2,
                  independent_algorithm='exact Python Buchberger, grevlex, prime-field arithmetic',
                  baseline_sha256=hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
                  candidate_sha256=hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
                  full_t_board_runs=0, results=results)
    (ROOT/'experiments'/(args.artifact_prefix+'_results.json')).write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'results'}, indent=2))


if __name__ == '__main__':
    main()
