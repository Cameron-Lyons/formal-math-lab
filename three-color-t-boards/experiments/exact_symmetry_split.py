#!/usr/bin/env python3
"""Complete cap-orbit manifests and fail-closed exact-count aggregation.

This module does not search ternary boards. The cap is the first two rows,
flattened as (top, left, middle, right). Its orbit weights are not uniform.
Only audited COMPLETE backend artifacts can enter the command-line aggregate.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import itertools
import json
from math import factorial, isqrt
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SCOPE = 'raw labeled fixed-prefix completions'


class AuditError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def json_digest(data):
    return digest(json.dumps(data, sort_keys=True, separators=(',', ':')).encode())


def read_json(path):
    def unique_keys(items):
        result = {}
        for key, value in items:
            require(key not in result, f'duplicate JSON key: {key}')
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_keys)


def cartesian_reflection(flat):
    """Reflect the actual coordinates (row,x), independently of CNF mirrors."""
    rows = isqrt(len(flat))
    require(rows * rows == len(flat), 'reflection needs complete rows')
    coordinates = {(r, x): flat[r*r+x+r]
                   for r in range(rows) for x in range(-r, r+1)}
    return ''.join(coordinates[r, -x]
                   for r in range(rows) for x in range(-r, r+1))


def orbit(flat, colors):
    require(all(c in '012'[:colors] for c in flat), 'invalid color')
    images = (flat, cartesian_reflection(flat))
    return sorted({''.join(str(permutation[int(c)]) for c in image)
                   for permutation in itertools.permutations(range(colors))
                   for image in images})


def generate_manifest(colors=3):
    require(type(colors) is int and colors in (2, 3), 'colors must be 2 or 3')
    all_caps = {''.join(map(str, cap))
                for cap in itertools.product(range(colors), repeat=4)}
    remaining = set(all_caps)
    cases = []
    group_order = 2 * factorial(colors)
    while remaining:
        representative = min(remaining)
        members = orbit(representative, colors)
        require(set(members) <= remaining, 'cap orbits overlap')
        weight = len(members)
        require(group_order % weight == 0, 'invalid orbit size')
        cases.append(dict(representative=representative,
                          prefix_rows=[representative[0], representative[1:]],
                          orbit_weight=weight, orbit_members=members,
                          stabilizer_order=group_order // weight))
        remaining.difference_update(members)
    require(sum(case['orbit_weight'] for case in cases) == colors**4,
            'cap partition incomplete')
    result = dict(format='t-board-cap-orbits-v1', colors=colors,
                  board_rows=colors**2+1, fixed_rows=2, fixed_cells=4,
                  group='global palette permutations and horizontal reflection',
                  group_order=group_order, cap_count=colors**4,
                  representatives=len(cases), count_scope=SCOPE,
                  aggregation='sum(orbit_weight * raw_completion_count)',
                  cases=cases)
    result['manifest_sha256'] = json_digest(result)
    return result


def validate_manifest(manifest):
    require(isinstance(manifest, dict), 'manifest must be an object')
    require(manifest == generate_manifest(manifest.get('colors')),
            'manifest differs from complete independently generated partition')


@dataclass(frozen=True)
class VerifiedCount:
    """An in-memory count already verified by an artifact/complete-DFS audit."""
    prefix: str
    model: str
    colors: int
    board_rows: int
    count: int
    provenance: dict
    status: str = 'COMPLETE'
    count_scope: str = SCOPE
    count_multiplier: int = 1
    symmetry_normalization: bool = False


def aggregate(manifest, records, expected_model):
    """Refuse any partial, duplicate, unknown, or mismatched case collection."""
    validate_manifest(manifest)
    expected = {case['representative']: case for case in manifest['cases']}
    counts = {}
    for record in records:
        require(isinstance(record, VerifiedCount), 'count has not passed an audit')
        require(record.status == 'COMPLETE', f'{record.prefix}: status is not COMPLETE')
        require(record.model == expected_model, f'{record.prefix}: model mismatch')
        require(record.colors == manifest['colors'] and
                record.board_rows == manifest['board_rows'], 'board scope mismatch')
        require(record.count_scope == SCOPE and record.count_multiplier == 1 and
                record.symmetry_normalization is False, 'count is not a raw prefix fiber')
        require(record.prefix in expected, f'unknown or noncanonical prefix {record.prefix}')
        require(record.prefix not in counts, f'duplicate prefix {record.prefix}')
        require(type(record.count) is int and record.count >= 0, 'invalid exact integer count')
        require(bool(record.provenance), 'missing authoritative count provenance')
        counts[record.prefix] = record
    missing = sorted(expected.keys() - counts.keys())
    require(not missing, 'missing COMPLETE prefixes: ' + ', '.join(missing))
    terms = [dict(prefix=prefix, orbit_weight=case['orbit_weight'],
                  completion_count_decimal=str(counts[prefix].count),
                  weighted_count_decimal=str(case['orbit_weight'] * counts[prefix].count),
                  provenance=counts[prefix].provenance)
             for prefix, case in expected.items()]
    total = sum(int(term['weighted_count_decimal']) for term in terms)
    return dict(format='t-board-cap-aggregate-v1', status='COMPLETE',
                model=expected_model, colors=manifest['colors'],
                board_rows=manifest['board_rows'],
                manifest_sha256=manifest['manifest_sha256'],
                complete_cases=len(terms), cap_orbit_weights_sum=manifest['cap_count'],
                count_scope='full labeled boards', full_count_decimal=str(total),
                terms=terms)


@lru_cache(maxsize=32)
def expected_prime_definition(model, prefix):
    """Rebuild the expected fixed-prefix input without importing the backend."""
    from exact_prime_fourier import generate_model
    match = re.fullmatch(r'prime(-all)?:(\d+)', model)
    require(match is not None, 'only geometry-derived prime Fourier models are supported')
    prime = int(match[2])
    rows = isqrt(len(prefix))
    require(rows*rows == len(prefix), 'prefix must contain complete rows')
    data = generate_model(prime, [prefix[r*r:(r+1)**2] for r in range(rows)],
                          all_moments=bool(match[1]))
    n = data['variables']
    require(n > 0, 'artifact audit currently requires at least one free cell')
    equations = [f'x{i+1}^3-1' for i in range(n)]
    extension = False
    for equation in data['moment_equations']:
        terms = []
        for term in equation['terms']:
            u, v = term['coefficient']
            extension |= bool(v)
            coefficient = f'({u}+{v}*a)' if v else str(u)
            monomial = '*'.join(f'x{i+1}' + (f'^{e}' if e != 1 else '')
                                for i, e in term['monomial']) or '1'
            terms.append(coefficient + '*' + monomial)
        if terms:
            equations.append('+'.join(terms))
    coefficient_field = f'({prime},a)' if extension else str(prime)
    definition = f'ring R={coefficient_field},(' + ','.join(f'x{i+1}' for i in range(n)) + '),dp;\n'
    if extension:
        definition += 'minpoly=a^2+a+1;\n'
    definition += 'ideal I=\n' + ',\n'.join(equations) + ';\n'
    metadata = dict(field=f'F{prime}' + ('^2' if extension else ''),
                    characteristic=prime, variables=n, generators=len(equations),
                    fourier_moments=len(data['moment_equations']),
                    free_original_cells=data['free_original_cells'],
                    model_data_sha256=digest(json.dumps(data, sort_keys=True).encode()))
    return definition, metadata


def expected_backend_tail(algorithm):
    """Audited exact backend contract; no arbitrary intervening script is allowed."""
    require(algorithm in ('std', 'slimgb'), 'unsupported standard-basis algorithm')
    return ('option(redSB);\nprint("GB_STARTED");\nideal G=' + algorithm + '(I);\n'
            'print("GB_COMPLETE");\n'
            'print("BASIS_IS_STANDARD="+string(attrib(G,"isSB")));\n'
            'print("KRULL_DIM="+string(dim(G)));\nprint("BASIS_SIZE="+string(size(G)));\n'
            'for(int k=1;k<=size(G);k++){if(G[k]==0){ERROR("zero polynomial in standard basis export");}print("LM="+string(leadexp(G[k])));}\n'
            'print("LM_COMPLETE");\nprint("HILB_STARTED");\n'
            'bigintvec H=hilb(G,2);\nprint("HILB_TYPE="+typeof(H));\n'
            'bigint D=0;\nfor(int j=1;j<size(H);j++){D=D+H[j];}\n'
            'print("HILB_DIM="+string(D));\nprint("BACKEND_COMPLETE");\nquit;\n')


def resolve_artifact(path):
    result = Path(path)
    return result if result.is_absolute() else ROOT / result


def audit_backend_result(path, expected_model, expected_prefix, *, max_states=1000000):
    """Verify one COMPLETE prime-prefix result and its retained exact artifacts.

    A completed standard basis is trusted as a backend result, not re-proved
    here. Its leading ideal is independently recounted with Python integers.
    The cap aggregator additionally requires the audited prefix to have four cells.
    """
    path = resolve_artifact(path)
    data = read_json(path)
    require(data.get('status') == 'COMPLETE', 'backend status is not COMPLETE')
    require(data.get('model') == expected_model, 'backend model mismatch')
    require(data.get('prefix') == expected_prefix, 'backend prefix mismatch')
    require(data.get('basis_complete') is True, 'standard basis incomplete')
    for flag in ('standard_basis_complete', 'leading_export_complete', 'dimension_complete'):
        require(data.get(flag, True) is True, f'{flag} is false')
    require(data.get('returncode') == 0 and data.get('wall_timeout_reached') is False,
            'backend did not finish normally')
    require(not data.get('error_diagnostics') and not data.get('postprocess_error'),
            'backend error diagnostics present')
    require(data.get('ring_type') == 'ordinary polynomial ring' and
            data.get('ordering') == 'dp', 'unexpected ring or ordering')
    for flag in ('normalize_apex', 'palette_canonical', 'orbit_canonical', 'symmetry_normalization'):
        require(not data.get(flag), f'unexpected symmetry restriction: {flag}')
    require(data.get('unrestricted_multiplier', 1) == 1 and data.get('count_multiplier', 1) == 1,
            'prefix result carries a multiplier')
    require(data.get('count_scope', 'extensions of fixed prefix') == 'extensions of fixed prefix',
            'wrong count scope')
    require(data.get('fixed_prefix_rows', isqrt(len(expected_prefix))) == isqrt(len(expected_prefix)) and
            data.get('fixed_cell_count', len(expected_prefix)) == len(expected_prefix) and
            data.get('fixed_original_cells', list(range(len(expected_prefix)))) == list(range(len(expected_prefix))),
            'fixed prefix metadata mismatch')
    definition, expected = expected_prime_definition(expected_model, expected_prefix)
    for key, value in expected.items():
        require(data.get(key) == value, f'generated model metadata mismatch: {key}')
    require(data.get('color_map') == ['1', 'a', '-a-1'], 'wrong color map')
    script_path = resolve_artifact(data['script'])
    script = script_path.read_bytes()
    require(digest(script) == data.get('script_sha256'), 'script hash mismatch')
    require(script.decode() == definition + expected_backend_tail(data.get('algorithm')),
            'actual script differs from expected prefix model/count procedure')
    log_path = path.with_suffix('.log')
    log = log_path.read_text()
    require(not any(line.lstrip().startswith('?') or
                    re.search(r'\berror\b|overflow|segmentation fault|aborted', line, re.I)
                    for line in log.splitlines()), 'error diagnostic in actual log')
    for marker in ('GB_COMPLETE', 'LM_COMPLETE', 'BACKEND_COMPLETE'):
        require(log.splitlines().count(marker) == 1, f'missing or duplicated log marker: {marker}')
    fields = {}
    for line in log.splitlines():
        if re.match(r'^(BASIS_IS_STANDARD|BASIS_SIZE|KRULL_DIM|HILB_TYPE|HILB_DIM)=', line):
            key, value = line.split('=', 1)
            require(key not in fields, f'duplicate log field: {key}')
            fields[key] = value
    require(fields.get('BASIS_IS_STANDARD') == '1' and fields.get('HILB_TYPE') == 'bigintvec',
            'missing standard-basis or exact bigint Hilbert attestation')
    exact = data.get('quotient_dimension')
    require(type(exact) is int and exact >= 0 and data.get('dimension_decimal') == str(exact),
            'invalid or inconsistent exact count')
    for key in ('monomial_dimension', 'independent_monomial_dimension', 'hilbert_dimension'):
        require(type(data.get(key)) is int and data[key] == exact, f'count disagreement: {key}')
    require(fields.get('HILB_DIM') == str(exact), 'count differs from exact Hilbert log')
    require(fields.get('KRULL_DIM') == str(data.get('krull_dimension')) and
            data.get('krull_dimension') in ((-1, 0) if exact == 0 else (0,)),
            'positive-dimensional or inconsistent quotient')
    leading = [list(map(int, line[3:].split(',')))
               for line in log.splitlines() if line.startswith('LM=')]
    require(len(leading) == data.get('basis_size') and fields.get('BASIS_SIZE') == str(len(leading)),
            'incomplete leading-monomial list')
    leading_path = resolve_artifact(data['leading_monomials_file'])
    exported = read_json(leading_path)
    require(exported.get('format') == 'leading-monomial-ideal-v1' and
            exported.get('standard_basis_complete') is True and
            exported.get('variables') == expected['variables'] and
            exported.get('leading_monomials') == leading, 'leading export mismatch')
    provenance = exported.get('provenance', {})
    require(provenance.get('script_sha256') == digest(script) and
            provenance.get('algorithm') == data.get('algorithm') and
            provenance.get('field') == data.get('field'), 'leading export provenance mismatch')
    from exact_standard_monomials import count_standard_monomials
    recounted = count_standard_monomials(leading, variables=expected['variables'],
                                        standard_basis_complete=True, max_states=max_states)
    require(recounted == exact, 'independent leading-ideal recount disagrees')
    return VerifiedCount(expected_prefix, expected_model, 3, 10, exact,
                         dict(method='audited-completed-standard-basis',
                              result=str(path.resolve()), result_sha256=digest(path.read_bytes()),
                              script_sha256=digest(script), log_sha256=digest(log.encode()),
                              leading_sha256=digest(leading_path.read_bytes()),
                              independently_recounted=True))


def enumerate_binary():
    """Exhaust all binary boards, pruning only after an already repeated T."""
    flat = [0] * 25
    boards = []
    visited = 0
    placement_at = {}
    for row in range(1, 5):
        for column in range(-row+1, row):
            positions = ((row-1)**2+column+(row-1),
                         row*row+column-1+row,
                         row*row+column+row,
                         row*row+column+1+row)
            placement_at[positions[-1]] = positions

    def visit(position, used):
        nonlocal visited
        visited += 1
        if position == 25:
            require(used.bit_count() == 16, 'complete board misses a pattern')
            boards.append(''.join(map(str, flat)))
            return
        for color in range(2):
            flat[position] = color
            next_used = used
            if position in placement_at:
                pattern = 0
                for cell in placement_at[position]:
                    pattern = 2*pattern + flat[cell]
                bit = 1 << pattern
                if used & bit:
                    continue
                next_used |= bit
            visit(position+1, next_used)

    visit(0, 0)
    return boards, dict(visited_partial_assignments=visited,
                       enumeration='both colors at every cell; prune only repeated completed T')


def witness_coverage():
    manifest = generate_manifest(3)
    sources = {
        'published': (ROOT/'sources/anc/certificates.json', lambda data:
                      [''.join(rows) for rows in data['ternary_seeds']]),
        'extended': (ROOT/'extended_seeds.json', lambda data:
                     [''.join(entry['rows']) for entry in data]),
        'gauge': (ROOT/'experiments/exact_structure_gauge_certificate.json', lambda data:
                  [entry['flat'] for entry in data['boards']])}
    union = set()
    reports = {}
    for name, (path, extract) in sources.items():
        boards = set(extract(read_json(path)))
        union.update(boards)
        reports[name] = dict(path=str(path.relative_to(ROOT)), sha256=digest(path.read_bytes()),
                             distinct_boards=len(boards), cap_orbit_witnesses={})
        for board in boards:
            require(len(board) == 100 and set(board) <= set('012'), 'malformed witness')
            patterns = {board[(r-1)**2+j] + board[r*r+j:r*r+j+3]
                        for r in range(1, 10) for j in range(2*r-1)}
            require(len(patterns) == 81, 'invalid witness in coverage input')
        counts = Counter(orbit(board[:4], 3)[0] for board in boards)
        reports[name]['cap_orbit_witnesses'] = {
            case['representative']: counts[case['representative']] for case in manifest['cases']}
    counts = Counter(orbit(board[:4], 3)[0] for board in union)
    return dict(format='t-board-cap-witness-coverage-v1', status='COVERAGE_ONLY',
                count_scope='saved explicit witnesses; not completion counts',
                distinct_boards=len(union), sources=reports,
                cases=[dict(prefix=case['representative'], witness_boards=counts[case['representative']],
                            covered=bool(counts[case['representative']])) for case in manifest['cases']],
                absent_does_not_imply_impossible=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    manifest_parser = commands.add_parser('manifest')
    manifest_parser.add_argument('--colors', type=int, choices=(2, 3), default=3)
    coverage_parser = commands.add_parser('coverage')
    aggregate_parser = commands.add_parser('aggregate')
    aggregate_parser.add_argument('--manifest', type=Path, required=True)
    aggregate_parser.add_argument('--model', default='prime-all:29')
    aggregate_parser.add_argument('results', type=Path, nargs='*')
    for command in (manifest_parser, coverage_parser, aggregate_parser):
        command.add_argument('--output', type=Path)
    args = parser.parse_args()
    failed = False
    try:
        if args.command == 'manifest':
            result = generate_manifest(args.colors)
        elif args.command == 'coverage':
            result = witness_coverage()
        else:
            manifest = read_json(args.manifest)
            validate_manifest(manifest)
            allowed = {case['representative'] for case in manifest['cases']}
            records = []
            seen = set()
            for path in args.results:
                metadata = read_json(path)
                prefix = metadata.get('prefix')
                require(prefix in allowed, f'result has wrong/noncanonical cap prefix: {prefix}')
                require(prefix not in seen, f'duplicate cap result: {prefix}')
                seen.add(prefix)
                records.append(audit_backend_result(path, args.model, prefix))
            result = aggregate(manifest, records, args.model)
    except (AuditError, OSError, KeyError, TypeError, ValueError, RuntimeError) as exc:
        failed = True
        result = dict(status='REFUSED', reason=str(exc), exact_total_available=False)
    serialized = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(serialized)
    print(serialized, end='')
    if failed:
        raise SystemExit(2)


if __name__ == '__main__':
    main()
