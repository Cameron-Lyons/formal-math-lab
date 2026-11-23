#!/usr/bin/env python3
"""Independent msolve adapter checks; no actual msolve process is started."""
from collections import defaultdict
import itertools
import json
from pathlib import Path
import random
import re
import subprocess
import tempfile
from unittest.mock import patch

import exact_msolve_backend as backend

ROOT = Path(__file__).resolve().parents[1]


def parse_polynomial(text, variables, prime):
    result = defaultdict(int)
    for signed in re.findall(r'[+-]?[^+-]+', text):
        coefficient = -1 if signed.startswith('-') else 1
        powers = [0]*variables
        for factor in signed.lstrip('+-').split('*'):
            if factor.isdigit():
                coefficient *= int(factor)
            else:
                match = re.fullmatch(r'x([1-9]\d*)(?:\^([1-9]\d*))?', factor)
                assert match, factor
                index = int(match[1])-1
                assert 0 <= index < variables
                powers[index] += int(match[2] or 1)
        result[tuple(powers)] += coefficient
    return {key: value % prime for key, value in result.items() if value % prime}


def expected_polynomials(prime, prefix):
    """Rebuild all geometry and integer root multiplicities independently."""
    fixed = list(map(int, prefix))
    free = 100-len(fixed)
    moments = []
    for exponents in itertools.product(range(3), repeat=4):
        if not any(exponents):
            continue
        terms = defaultdict(lambda: [0, 0])
        for lower_row in range(1, 10):
            for center in range(-lower_row+1, lower_row):
                cells = ((lower_row-1)**2+center+lower_row-1,
                         lower_row**2+center-1+lower_row,
                         lower_row**2+center+lower_row,
                         lower_row**2+center+1+lower_row)
                powers = [0]*free
                fixed_exponent = 0
                for cell, exponent in zip(cells, exponents):
                    if cell < len(fixed):
                        fixed_exponent += fixed[cell]*exponent
                    else:
                        powers[cell-len(fixed)] += exponent
                u, v = ((1, 0), (0, 1), (-1, -1))[fixed_exponent % 3]
                pair = terms[tuple(powers)]
                pair[0] += u
                pair[1] += v
        moments.append({powers: (u % prime, v % prime)
                        for powers, (u, v) in terms.items() if u % prime or v % prime})
    extension = any(v for terms in moments for u, v in terms.values())
    variables = max(1, free+int(extension))
    zero = (0,)*variables
    result = []
    for i in range(free):
        powers = [0]*variables; powers[i] = 3
        result.append({tuple(powers): 1, zero: prime-1})
    if extension:
        linear = [0]*variables; linear[free] = 1
        square = [0]*variables; square[free] = 2
        result.append({zero: 1, tuple(linear): 1, tuple(square): 1})
    elif not free:
        result.append({(1,): 1})
    for terms in moments:
        ordinary = defaultdict(int)
        for powers, (u, v) in terms.items():
            padded = powers+(0,)*(variables-free)
            ordinary[padded] += u
            if v:
                with_a = list(padded); with_a[free] += 1
                ordinary[tuple(with_a)] += v
        normalized = {powers: coefficient % prime for powers, coefficient in ordinary.items()
                      if coefficient % prime}
        if normalized:
            result.append(normalized)
    return variables, extension, result


def mul(x, y, prime):
    u, v = x; s, t = y
    return ((u*s-v*t) % prime, (u*t+v*s-v*t) % prime)


def leading_text(variables=1, prime=29, terms=('x1^3',)):
    return ('#Leading ideal data\n#---\n'
            f'#field characteristic: {prime}\n'
            '#variable order: '+', '.join(f'x{i+1}' for i in range(variables))+'\n'
            '#monomial order: graded reverse lexicographical\n'
            f'#length of basis: {len(terms)} elements sorted by increasing leading monomials\n'
            '#---\n['+',\n'.join(terms)+']:\n')


def main():
    rng = random.Random(0x4D534F4C5645)
    certificates = json.loads((ROOT/'sources/anc/certificates.json').read_text())
    valid = ''.join(certificates['ternary_seeds'][0])
    invalid = ''.join(json.loads((ROOT/'experiments/exact_structure_counterexample.json').read_text())['rows'])
    random_board = ''.join(str(rng.randrange(3)) for _ in range(100))
    prefixes = ['', '0', '1', '2', '0000', '0001', '0012']
    prefixes += [random_board[:9], random_board[:81], random_board, valid[:81], valid, invalid]
    field_reports = []
    polynomial_comparisons = 0
    for prime in (5, 29, 83):
        for prefix in prefixes:
            source, metadata = backend.definitions(prime=prime, prefix=prefix)
            lines = source.splitlines()
            names, characteristic = lines[:2]
            n, extension, expected = expected_polynomials(prime, prefix)
            assert names == ','.join(f'x{i+1}' for i in range(n))
            assert int(characteristic) == prime
            actual = [parse_polynomial(text, n, prime)
                      for text in ''.join(lines[2:]).split(',')]
            assert actual == expected, (prime, prefix)
            assert metadata['variables'] == n and metadata['generators'] == len(expected)
            assert metadata['extension_variable'] == extension
            assert metadata['count_divisor'] == (2 if extension else 1)
            polynomial_comparisons += len(expected)
        roots = ((1, 0), (0, 1), (prime-1, prime-1))
        a_roots = roots[1:]
        assert all(mul(mul(x, x, prime), x, prime) == (1, 0) for x in roots)
        assert all(((mul(a, a, prime)[0]+a[0]+1) % prime,
                    (mul(a, a, prime)[1]+a[1]) % prime) == (0, 0) for a in a_roots)
        pair_domain = sum(1 for a, x in itertools.product(a_roots, roots))
        coupled = sum(x == a for a, x in itertools.product(a_roots, roots))
        conjugate_coupled = sum(x == mul(a, a, prime) for a, x in itertools.product(a_roots, roots))
        triple_sum = sum((sum(x[0] for x in triple) % prime,
                          sum(x[1] for x in triple) % prime) == (0, 0)
                         for a in a_roots for triple in itertools.product(roots, repeat=3))
        assert (pair_domain, coupled, conjugate_coupled, triple_sum) == (6, 2, 2, 12)
        field_reports.append(dict(prime=prime, scalar_extension_fixtures=[6, 2, 2, 12],
                                  after_divisor_two=[3, 1, 1, 6]))

    good = leading_text(2, terms=('x1^3', 'x2^3'))
    assert backend.parse_leading(good, 2, 29) == [[3, 0], [0, 3]]
    assert backend.parse_leading(leading_text(terms=('1',)), 1, 29) == [[0]]
    malformed = {
        'missing-marker': good.replace('#Leading ideal data\n', ''),
        'wrong-marker': good.replace('#Leading ideal data', '#Reduced Groebner basis data'),
        'duplicate-marker': good+'#Leading ideal data\n',
        'duplicate-characteristic': good+'#field characteristic: 2\n',
        'duplicate-monomial-order': good+'#monomial order: lex\n',
        'diagnostic-comment': good+'# ERROR: export failed\n',
        'unknown-comment': good+'# unfinished export\n',
        'missing-list-terminator': good.replace(']:', ']'),
        'missing-list-end': good.replace(']:', ''),
        'wrong-count': good.replace('2 elements', '3 elements'),
        'wrong-characteristic': good.replace('characteristic: 29', 'characteristic: 5'),
        'wrong-variable-order': good.replace('x1, x2', 'x2, x1'),
        'wrong-order': good.replace('graded reverse lexicographical', 'lexicographical'),
        'extra-payload': good+'[1]:\n',
        'zero-generator': good.replace('x1^3,', '0,'),
        'polynomial-not-monomial': good.replace('x1^3,', 'x1^3+1,'),
        'unknown-variable': good.replace('x1^3,', 'x3^3,'),
        'repeated-factor': good.replace('x1^3,', 'x1*x1^2,'),
        'negative-exponent': good.replace('x1^3,', 'x1^-3,'),
        'zero-exponent': good.replace('x1^3,', 'x1^0,')}
    rejected = []
    for name, output in malformed.items():
        try:
            backend.parse_leading(output, 2, 29)
        except ValueError:
            rejected.append(name)
        else:
            raise AssertionError('parser accepted: '+name)

    outcomes = []
    with tempfile.TemporaryDirectory(prefix='exact_msolve_review_') as directory:
        directory = Path(directory)
        executable = directory/'fake-msolve'
        executable.write_bytes(b'not executed: subprocess.run is mocked')
        for case, returncode, diagnostic, payload, timeout, expected in (
                ('complete', 0, '', leading_text(), False, 'COMPLETE'),
                ('unit', 0, '', leading_text(terms=('1',)), False, 'COMPLETE'),
                ('nonzero-exit', 1, '', leading_text(), False, 'BACKEND_ERROR'),
                ('error-log', 0, 'error: allocation failed', leading_text(), False, 'BACKEND_ERROR'),
                ('truncated-list', 0, '', leading_text().replace(']:', ''), False, 'POSTPROCESS_ERROR'),
                ('timeout-with-complete-file', 0, '', leading_text(), True, 'INCOMPLETE_TIMEOUT')):
            output = directory/case
            def fake_process(command, **kwargs):
                Path(command[command.index('-o')+1]).write_text(payload)
                log = 'MSOLVE_PRIME_GB_EXPORT_COMPLETE\n'+diagnostic
                if timeout:
                    raise subprocess.TimeoutExpired(command, 0.1, output=log)
                return subprocess.CompletedProcess(command, returncode, stdout=log, stderr='')
            with patch.object(backend.subprocess, 'run', side_effect=fake_process):
                result = backend.run(output, fixture='domain', executable=executable, seconds=1)
            assert result['status'] == expected, (case, result)
            if expected == 'COMPLETE':
                assert result['board_count_decimal'] == ('0' if case == 'unit' else '3')
            else:
                assert 'board_count_decimal' not in result
            outcomes.append(dict(case=case, status=result['status']))
        for case, markers, expected in (
                ('patched-one-marker', 1, 'COMPLETE'),
                ('patched-missing-marker', 0, 'BACKEND_ERROR'),
                ('patched-duplicate-marker', 2, 'BACKEND_ERROR')):
            output = directory/case
            def fake_marked_process(command, **kwargs):
                Path(command[command.index('-o')+1]).write_text(leading_text())
                return subprocess.CompletedProcess(command, 0,
                           stdout='MSOLVE_PRIME_GB_EXPORT_COMPLETE\n'*markers, stderr='')
            with patch.object(backend.subprocess, 'run', side_effect=fake_marked_process):
                result = backend.run(output, fixture='domain', executable=executable,
                                     seconds=1, require_export_marker=True)
            assert result['status'] == expected and result['export_marker_count'] == markers
            if expected != 'COMPLETE':
                assert result['basis_complete'] is False and 'board_count_decimal' not in result
                assert not output.with_suffix('.leading.json').exists()
            outcomes.append(dict(case=case, status=result['status']))
        prior = directory/'prior'
        prior.with_suffix('.ms').write_text('preserve original input')
        prior.with_suffix('.basis').write_text('preserve original basis')
        try:
            backend.run(prior, fixture='domain', executable=executable)
        except ValueError:
            pass
        else:
            raise AssertionError('existing artifacts accepted')
        assert prior.with_suffix('.ms').read_text() == 'preserve original input'
        assert prior.with_suffix('.basis').read_text() == 'preserve original basis'

    report = dict(status='PASS', backend_sha256=backend.sha256(Path(backend.__file__).read_bytes()),
                  geometry_models_checked=len(prefixes)*3,
                  independent_polynomial_comparisons=polynomial_comparisons,
                  field_extension_fixtures=field_reports, malformed_parser_cases_rejected=rejected,
                  mocked_process_outcomes=outcomes, rejected_rerun_preserves_prior_artifacts=True,
                  actual_solver_processes_started=0,
                  note='Mock COMPLETE results test control flow only; they are not solver counts or new board results.')
    (ROOT/'experiments/exact_msolve_review_results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
