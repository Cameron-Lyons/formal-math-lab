#!/usr/bin/env python3
"""Independent byte-build source, complete-basis, and fail-closed CLI review.

Never runs a board model. Small reference bases use Python integer Buchberger
and exhaustive F3 point enumeration, independent of either native executable.
"""
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import re
import resource
import subprocess

from exact_msolve_sparse_review import buchberger, leading, parse_full_basis, parse_polynomial, reduce_polynomial
from exact_standard_monomials import count_standard_monomials
from exact_msolve_backend import parse_leading

HERE = Path(__file__).resolve().parent
TREE = 'msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2'
CANDIDATE_HASH = '63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76'
PATCH_HASH = 'b97f1f487c27c2a0ddf7641046c36d118451a6231ce3554a69be25e0f24f04c6'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3,) * 2)
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def main():
    old_root = HERE / 'exact_msolve_symbolic_reserve_tools'
    root = HERE / 'exact_msolve_byte_exponent_tools'
    old, new = old_root / TREE / 'src', root / TREE / 'src'
    manifest = json.loads((root / 'source.json').read_text())
    assert sha(root / 'msolve') == manifest['executable_sha256'] == CANDIDATE_HASH
    assert sha(root / 'checked-byte-exponents.patch') == manifest['checked_byte_patch_sha256'] == PATCH_HASH
    changed = []
    for p in sorted(old.rglob('*')):
        if p.suffix not in ('.c', '.h'):
            continue
        rel = p.relative_to(old)
        assert (new / rel).exists()
        if p.read_bytes() != (new / rel).read_bytes():
            changed.append(str(rel))
    assert changed == ['msolve/main.c', 'neogb/data.h', 'neogb/engine.c', 'neogb/hash.c', 'neogb/io.c', 'neogb/symbol.c']
    added = sorted(str(p.relative_to(new)) for p in new.rglob('*')
                   if p.suffix in ('.c', '.h') and not (old / p.relative_to(new)).exists())
    assert added == ['msolve/byte_input_guard.h', 'neogb/byte_model_guard.h']
    for name, expected in manifest['modified_source_sha256'].items():
        assert sha(root / TREE / name) == expected, name
    main_source = (new / 'msolve/main.c').read_text()
    assert main_source.index('byte_validate_file(files->in_file);') < main_source.index('get_data_from_file(files->in_file')
    assert main_source.index('get_data_from_file(files->in_file') < main_source.index('checked_byte_model(gens->lens')
    io_source = (new / 'neogb/io.c').read_text()
    common_import = io_source[io_source.index('void import_input_data('):]
    assert common_import.index('checked_byte_model(') < common_import.index('set_exponent_vector(')

    output = HERE / 'exact_msolve_byte_review_runs'
    output.mkdir(exist_ok=False)
    env = dict(os.environ, LD_LIBRARY_PATH=str(HERE / 'exact_algebra_backend_root/usr/lib'))
    fields = lambda n: [f'x{i+1}^3+2*x{i+1}' for i in range(n)]
    fixtures = [
        ('two-cube-lcm-degree6', 2, fields(2)),
        ('field-domains', 4, fields(4)),
        ('signed-sum', 3, fields(3) + ['x1+2*x2+x3']),
        ('nonzero-product', 3, fields(3) + ['x1*x2*x3+2']),
        ('mixed-chain', 4, fields(4) + ['x1*x2+2*x3', 'x2*x3+2*x4']),
        ('dense-quadratic', 3, fields(3) + ['1+x1*x2+2*x1*x3+x2*x3']),
        ('quadratic-pair', 3, fields(3) + ['x1*x2+2*x3^2', 'x1^2*x2^2+2*x3']),
        ('unit', 1, fields(1) + ['x1', 'x1+1']),
        ('dense-chain', 4, fields(4) + ['x1*x2+x2*x3+2*x3*x4+1', 'x1^2+2*x2*x4+x3+1']),
        ('scaled-reversed-domains', 2, ['x1+2*x1^3', '2*x2+x2^3', 'x1+x2']),
        ('boundary-int32-coefficients', 2, fields(2) + ['2147483647*x1-2147483647*x2']),
        ('zero-duplicate-domains', 2, fields(2) + fields(2) + ['0']),
    ]
    rng = random.Random(63052125)
    for k in range(8):
        equations = fields(3)
        for _ in range(1 + k % 2):
            exponents = rng.sample(list(itertools.product(range(3), repeat=3)), 7)
            terms = []
            for exps in exponents:
                factors = [f'x{i+1}' + (f'^{e}' if e != 1 else '') for i, e in enumerate(exps) if e]
                terms.append('*'.join([str(rng.randrange(1, 3))] + factors))
            equations.append('+'.join(terms))
        fixtures.append((f'seeded-mixed-{k}', 3, equations))

    def run(name, text, executable, mode=2, extra=()):
        stem = output / name
        stem.with_suffix('.ms').write_text(text)
        command = [str(executable), '-g', str(mode), '-l', '2', '-t', '1', '-r', '1', '-c', '0',
                   '-v', '2', '-m', '16', '-s', '4', '-f', str(stem.with_suffix('.ms')),
                   '-o', str(stem.with_suffix('.basis')), *extra]
        done = subprocess.run(command, capture_output=True, text=True, timeout=15, env=env, preexec_fn=limits)
        log = done.stdout + done.stderr
        stem.with_suffix('.log').write_text(log)
        return stem, done, log, command

    reports = []
    for name, n, equations in fixtures:
        text = ','.join(f'x{i+1}' for i in range(n)) + '\n3\n' + ',\n'.join(equations) + '\n'
        original = [parse_polynomial(e, n, 3) for e in equations]
        reference = buchberger(original, 3)
        assert all(not reduce_polynomial(p, reference, 3) for p in original)
        def value(poly, point):
            return sum(c * __import__('math').prod(pow(x, e, 3) for x, e in zip(point, m)) for m, c in poly.items()) % 3
        direct = sum(all(value(p, point) == 0 for p in original) for point in itertools.product(range(3), repeat=n))
        dimension = count_standard_monomials([leading(p) for p in reference], n, standard_basis_complete=True)
        assert dimension == direct
        runs = []
        for mode in (1, 2):
            exports = []
            for label, exe in [('seventh', old_root / 'msolve'), ('byte', root / 'msolve')]:
                stem, done, log, command = run(f'{name}_{label}_g{mode}', text, exe, mode)
                assert done.returncode == 0, (name, label, log[-1500:])
                assert log.splitlines().count('MSOLVE_PRIME_GB_EXPORT_COMPLETE') == 1
                assert not re.search(r'\berror\b|failed|out of memory|segmentation|cannot allocate', log, re.I)
                assert 'MSOLVE_F2_BITSET rows=' not in log
                body = stem.with_suffix('.basis').read_text()
                if mode == 2:
                    assert parse_full_basis(body, n, 3) == reference, (name, label)
                else:
                    assert sorted(map(tuple, parse_leading(body, n, 3))) == sorted(leading(p) for p in reference)
                exports.append(body)
                runs.append(dict(label=label, mode=mode, command=command, returncode=done.returncode,
                                 basis_sha256=sha(stem.with_suffix('.basis')),
                                 symbolic_reserves=log.count('MSOLVE_SYMBOLIC_ROW_RESERVE '),
                                 staging_rounds=log.count('MSOLVE_SYMBOLIC_STAGING ')))
            assert exports[0] == exports[1]
        reports.append(dict(name=name, variables=n, generators=len(equations), input_sha256=hashlib.sha256(text.encode()).hexdigest(),
                            direct_F3_count=direct, quotient_dimension_decimal=str(dimension),
                            full_basis_matches_python=True, leading_basis_matches_python=True,
                            exports_byte_identical_to_seventh=True, runs=runs))

    base = 'x1,x2\n3\nx1^3+2*x1,x2^3+2*x2\n'
    bad_inputs = [
        ('missing-second-domain', 'x1,x2\n3\nx1^3+2*x1,x2^2\n'),
        ('split-domain-is-insufficient', 'x1\n3\nx1^3,2*x1\n'),
        ('zero-scalar-domain', 'x1\n3\n3*x1^3+3*x1\n'),
        ('cross-variable-domain', 'x1,x2\n3\nx1^3+2*x2,x2^3+2*x1\n'),
        ('wrong-sign-domain', base.replace('2*x2', 'x2')),
        ('cubic-nondomain', base + ',x1^3+x2^2\n'),
        ('exponent-256', base + ',x1^256\n'),
        ('exponent-wrap', base + ',x1^4294967297\n'),
        ('negative-exponent', base + ',x1^-1\n'),
        ('coefficient-wrap', base + ',4294967297*x1\n'),
        ('negative-coefficient-overflow', base + ',-2147483648*x1\n'),
        ('duplicate-factor', base + ',x1*x1\n'),
        ('missing-multiplication', base + ',2x1\n'),
        ('unknown-variable', base + ',x3\n'),
        ('leading-zero-variable', base + ',x01\n'),
        ('exponent-garbage', base + ',x1^2z\n'),
        ('rational', base + ',1/2*x1\n'),
        ('trailing-comma', base + ',\n'),
        ('wrong-field', base.replace('\n3\n', '\n2\n')),
        ('n128', ','.join(f'x{i+1}' for i in range(128)) + '\n3\n1\n'),
    ]
    rejects = []
    for name, text, extra in [(name, text, ()) for name, text in bad_inputs] + [
        ('cli-' + name, base, args) for name, args in [
            ('thread-wrap', ('-t', '4294967297')), ('thread2', ('-t', '2')),
            ('la-random', ('-l', '42')), ('signature', ('-q', '1')),
            ('signature-clamped', ('-q', '999')), ('normalform', ('-n', '0')),
            ('elimination', ('-e', '0')), ('no-reduction', ('-r', '0')),
            ('hash-too-large', ('-s', '27')), ('binary-input', ('-F', 'nonexistent')),
            ('saturation', ('-S',)), ('not-export', ('-g', '0')),
            ('noncanonical-option', ('-m', '+1')), ('option-overflow', ('-u', '2147483648'))]]:
        stem, done, log, command = run('reject-' + name, text, root / 'msolve', 1, extra)
        assert done.returncode != 0 and re.search(r'\bError\b', log), (name, done.returncode, log)
        assert 'MSOLVE_PRIME_GB_EXPORT_COMPLETE' not in log
        assert not stem.with_suffix('.basis').exists() or stem.with_suffix('.basis').stat().st_size == 0
        rejects.append(dict(name=name, returncode=done.returncode, command=command,
                            diagnostic=next(line for line in log.splitlines() if re.search(r'\bError\b', line))))
    report = dict(status='PASS', candidate_sha256=CANDIDATE_HASH, patch_sha256=PATCH_HASH,
                  changed_source_files=changed, added_source_files=added,
                  source_hashes_verified=manifest['modified_source_sha256'],
                  fixtures=len(reports), complete_native_runs=4*len(reports),
                  independent_Python_complete_bases=len(reports), exhaustive_F3_point_counts=len(reports),
                  rejection_cases=len(rejects), full_board_solver_runs=0, memory_limit_bytes=2*1024**3,
                  results=reports, rejections=rejects)
    (HERE / 'exact_msolve_byte_review_results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('results', 'rejections', 'source_hashes_verified')}, indent=2))


if __name__ == '__main__':
    main()
