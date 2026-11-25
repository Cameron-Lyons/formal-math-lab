#!/usr/bin/env python3
"""Audit msolve prefix artifacts before using the complete ten-cap partition.

No solver is run. A completed standard basis is a trusted backend result, not
an independently proved Groebner certificate. Input geometry, retained output,
integer staircase count, coefficient-field divisor, and the complete cap
partition are checked here. PREPARED, timeout, and partial results never count.
"""
from functools import lru_cache
from math import isqrt
from pathlib import Path
import argparse
import json
import re

from exact_msolve_backend import parse_leading
from exact_msolve_review import expected_polynomials, parse_polynomial
from exact_prime_fourier import validate_prime
from exact_standard_monomials import count_standard_monomials
from exact_symmetry_split import (ROOT, VerifiedCount, aggregate, digest,
                                  generate_manifest, read_json, require)

# These are separately reviewed export-only builds. An unreviewed executable
# cannot gain acceptance just by reporting its own hash in a result file.
REVIEWED_EXECUTABLES = {
    '2d3258dd099a34410b05eadd21dbb38db22b8be0962ab59115d01660652c355d',
    '997199fc836584627dc1c6324fc2702a4d900f4cee84d4534acd89f29a068093',
    '1e2111b5e1ef28201f3b2da6bc727d4563569e96b3468ab241433e7d2238a202',
    'cebd842aa617f09725a1f5429ebc822da238563f142b14993cccb85312d1874c',
    '78e65a3c746a036d12ac67d8c332a9afd2101746eee3b850d4a2ecb5e696f502',
}
ERROR = re.compile(r'\berror\b|out of memory|cannot allocate|segmentation|aborted', re.I)
MARKER = 'MSOLVE_PRIME_GB_EXPORT_COMPLETE'


def artifact(path):
    path = Path(path)
    return (path if path.is_absolute() else ROOT / path).resolve()


def model_name(prime):
    return f'msolve-prime-all:{validate_prime(prime)}'


@lru_cache(maxsize=24)
def expected_input(prime, prefix, pivot_order):
    """Independent centered geometry; no backend/generator polynomial reuse."""
    validate_prime(prime)
    require(isinstance(prefix, str) and 0 < len(prefix) <= 100 and
            isqrt(len(prefix)) ** 2 == len(prefix) and
            all(c in '012' for c in prefix), 'invalid complete-row prefix')
    require(type(pivot_order) is bool, 'invalid variable-order flag')
    variables, extension, original = expected_polynomials(prime, prefix)
    cells = list(range(len(prefix), 100))
    preferred = [c for c in (0, 81, 90, 99) if c in cells] if pivot_order else []
    order = preferred + [c for c in cells if c not in preferred]
    old_to_new = [order.index(c) for c in cells]
    free = len(cells)
    polynomials = []
    for j, polynomial in enumerate(original):
        # The initial free-cube list is written in the new ring's own order.
        if j < free:
            polynomials.append(polynomial)
            continue
        transformed = {}
        for powers, coefficient in polynomial.items():
            new = [0] * variables
            for i in range(free):
                new[old_to_new[i]] = powers[i]
            for i in range(free, variables):
                new[i] = powers[i]
            transformed[tuple(new)] = coefficient
        polynomials.append(transformed)
    return polynomials, dict(prime=prime, prefix=prefix, variables=variables,
        generators=len(polynomials), free_board_variables=free,
        extension_variable=extension, count_divisor=2 if extension else 1,
        dispersed_variable_order=pivot_order, variable_original_cells=order,
        scope='extensions of fixed prefix', moment_equations=80,
        field=f'F{prime}', ring_type='ordinary polynomial ring')


def audit_input(path, prime, prefix, pivot_order=False):
    """Check every ordinary polynomial against independently rebuilt geometry."""
    expected, metadata = expected_input(prime, prefix, pivot_order)
    raw = artifact(path).read_bytes()
    lines = raw.decode().splitlines()
    n = metadata['variables']
    require(len(lines) >= 3 and lines[0] == ','.join(f'x{i+1}' for i in range(n)),
            'input ring variable list mismatch')
    require(lines[1] == str(prime), 'input characteristic mismatch')
    pieces = '\n'.join(lines[2:]).split(',')
    require(len(pieces) == len(expected), 'input generator count mismatch')
    for i, (piece, wanted) in enumerate(zip(pieces, expected)):
        # Restrict the parser to the grammar the adapter actually emits.
        polynomial = ''.join(piece.split())
        require(re.fullmatch(r'[0-9x*^+\-]+', polynomial) is not None,
                f'unsupported input syntax at generator {i}')
        require(parse_polynomial(polynomial, n, prime) == wanted,
                f'input polynomial differs from geometry at generator {i}')
    return dict(metadata, source_sha256=digest(raw),
                independent_geometry_checked=True)


def decimal(value, label):
    require(isinstance(value, str) and re.fullmatch(r'0|[1-9][0-9]*', value),
            f'invalid exact decimal: {label}')
    return int(value)


def audit_msolve_result(path, prime, expected_prefix, *, max_states=1_000_000):
    """Return a raw fixed-prefix count only after complete artifact validation."""
    path = artifact(path)
    data = read_json(path)
    require(data.get('status') == 'COMPLETE', 'backend status is not COMPLETE')
    require(data.get('prefix') == expected_prefix, 'backend prefix mismatch')
    require(type(data.get('returncode')) is int and data['returncode'] == 0,
            'backend did not exit normally')
    require(data.get('basis_complete') is True, 'standard basis incomplete')
    require(data.get('require_export_marker') is True and
            data.get('export_marker_count') == 1, 'export attestation not required/present')
    require(data.get('error_diagnostics') == [] and not data.get('postprocess_error'),
            'backend error diagnostics present')
    require(data.get('linear_algebra') == 'exact sparse (-l 2)' and
            data.get('threads') == 1, 'unexpected backend arithmetic mode')
    for flag in ('normalize_apex', 'palette_canonical', 'orbit_canonical',
                 'symmetry_normalization', 'ternary_reduced', 'binary', 'fixture'):
        require(not data.get(flag), f'unexpected model restriction: {flag}')
    require(data.get('count_multiplier', 1) == 1 and
            data.get('unrestricted_multiplier', 1) == 1, 'unexpected count multiplier')
    input_path = path.with_suffix('.ms')
    require(artifact(data['input_file']) == input_path, 'input artifact path mismatch')
    expected = audit_input(input_path, prime, expected_prefix,
                           data.get('dispersed_variable_order', False))
    for key, value in expected.items():
        if key == 'independent_geometry_checked':
            continue
        # Original reviewed exports predate these two metadata-only fields;
        # their actual input still has to match the independently checked order.
        if key in ('dispersed_variable_order', 'variable_original_cells') and key not in data:
            require(not expected['dispersed_variable_order'], 'missing reordered variable map')
            continue
        require(data.get(key) == value, f'model metadata mismatch: {key}')
    command = data.get('command')
    require(isinstance(command, list) and len(command) == 19, 'unexpected command shape')
    require(command[1:13] == ['-g','1','-l','2','-t','1','-r','1','-c','0','-v','2'] and
            command[13] == '-m' and re.fullmatch(r'0|[1-9][0-9]*', command[14]) and
            command[15] == '-f' and artifact(command[16]) == input_path and
            command[17] == '-o' and artifact(command[18]) == path.with_suffix('.basis'),
            'command does not attest the expected exact input/export mode')
    executable_hash = data.get('executable_sha256')
    require(executable_hash in REVIEWED_EXECUTABLES, 'unreviewed executable')
    require(digest(artifact(command[0]).read_bytes()) == executable_hash,
            'executable hash mismatch')
    libraries = data.get('local_shared_libraries')
    require(isinstance(libraries, dict) and libraries, 'missing local-library provenance')
    for library, hashed in libraries.items():
        require(digest(artifact(library).read_bytes()) == hashed, 'local-library hash mismatch')
    log_path = path.with_suffix('.log')
    require(artifact(data.get('log_file', log_path)) == log_path, 'log artifact path mismatch')
    log = log_path.read_bytes()
    log_lines = log.decode().splitlines()
    require(sum(line.strip() == MARKER for line in log_lines) == 1,
            'missing/duplicate actual export-completion marker')
    require(not any(ERROR.search(line) for line in log_lines), 'error in actual solver log')
    basis = path.with_suffix('.basis').read_bytes()
    require(digest(basis) == data.get('basis_sha256'), 'basis hash mismatch')
    leading = parse_leading(basis.decode(), expected['variables'], prime)
    require(type(data.get('basis_size')) is int and data['basis_size'] == len(leading),
            'basis size mismatch')
    export_path = path.with_suffix('.leading.json')
    exported = read_json(export_path)
    require(exported == dict(format='leading-monomial-ideal-v1',
        variables=expected['variables'], standard_basis_complete=True,
        leading_monomials=leading, provenance=dict(backend='msolve F4',
            input_sha256=expected['source_sha256'], executable_sha256=executable_hash,
            field=expected['field'], linear_algebra='exact sparse')),
        'leading-ideal export/provenance mismatch')
    dimension = decimal(data.get('dimension_decimal'), 'quotient dimension')
    raw = decimal(data.get('board_count_decimal'), 'raw board count')
    require(dimension == expected['count_divisor'] * raw, 'coefficient-field divisor mismatch')
    recounted = count_standard_monomials(leading, expected['variables'],
        standard_basis_complete=True, max_states=max_states)
    require(recounted == dimension, 'independent integer staircase recount disagrees')
    return VerifiedCount(expected_prefix, model_name(prime), 3, 10, raw,
        dict(method='audited-msolve-completed-standard-basis', result=str(path),
             result_sha256=digest(path.read_bytes()), input_sha256=expected['source_sha256'],
             log_sha256=digest(log), basis_sha256=digest(basis),
             leading_sha256=digest(export_path.read_bytes()), executable_sha256=executable_hash,
             quotient_dimension_decimal=str(dimension), count_divisor=expected['count_divisor'],
             independent_geometry_checked=True, independently_recounted=True))


def aggregate_msolve(records, prime):
    manifest = generate_manifest(3)
    stabilizers = {c['representative']: c['stabilizer_order'] for c in manifest['cases']}
    records = list(records)
    for record in records:
        require(isinstance(record, VerifiedCount), 'count has not passed an audit')
        require(record.prefix in stabilizers, 'result is not a canonical two-row cap')
        require(record.count % stabilizers[record.prefix] == 0,
                'raw fiber count violates free full-board stabilizer action')
    return aggregate(manifest, records, model_name(prime))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prime', type=int, required=True)
    parser.add_argument('--result', action='append', default=[], metavar='PREFIX=JSON')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    records = []
    for item in args.result:
        prefix, path = item.split('=', 1)
        records.append(audit_msolve_result(path, args.prime, prefix))
    result = aggregate_msolve(records, args.prime)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        with args.output.open('x') as destination:
            destination.write(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
