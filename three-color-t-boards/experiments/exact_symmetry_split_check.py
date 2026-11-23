#!/usr/bin/env python3
"""Independent exhaustive binary and fail-closed cap aggregation checks."""
from collections import Counter
from copy import deepcopy
from dataclasses import replace
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import exact_symmetry_split as split

ROOT = Path(__file__).resolve().parents[1]


def main():
    rejected = []

    def refuses(name, function):
        try:
            function()
        except (split.AuditError, OSError, KeyError, ValueError, RuntimeError):
            rejected.append(name)
        else:
            raise AssertionError('incorrectly accepted: ' + name)

    manifests = {q: split.generate_manifest(q) for q in (2, 3)}
    assert len(manifests[2]['cases']) == 6 and len(manifests[3]['cases']) == 10
    expected_ternary = {'0000': 3, '0001': 12, '0010': 6, '0011': 12, '0012': 12,
                        '0101': 6, '0102': 6, '0111': 6, '0112': 12, '0121': 6}
    assert {case['representative']: case['orbit_weight']
            for case in manifests[3]['cases']} == expected_ternary
    checked_caps = 0
    for q, manifest in manifests.items():
        split.validate_manifest(manifest)
        membership = {}
        for case in manifest['cases']:
            for member in case['orbit_members']:
                assert member not in membership
                membership[member] = case['representative']
                # A direct positional action independent of Cartesian reflection.
                images = {''.join(str(p[int(c)]) for c in image)
                          for p in itertools.permutations(range(q))
                          for image in (member, member[0]+member[3]+member[2]+member[1])}
                assert images == set(case['orbit_members'])
                assert min(images) == case['representative']
                stabilizer = sum(''.join(str(p[int(c)]) for c in image) == member
                                 for p in itertools.permutations(range(q))
                                 for image in (member, member[0]+member[3]+member[2]+member[1]))
                assert stabilizer == case['stabilizer_order']
                checked_caps += 1
        assert len(membership) == q**4
        for case in manifest['cases']:
            assert case['prefix_rows'][0]+case['prefix_rows'][1] == case['representative']

    boards, enumeration_stats = split.enumerate_binary()
    assert len(set(boards)) == len(boards) == 168
    board_set = set(boards)
    for board in boards:
        patterns = {board[(r-1)**2+j] + board[r*r+j:r*r+j+3]
                    for r in range(1, 5) for j in range(2*r-1)}
        assert patterns == {''.join(map(str, p)) for p in itertools.product(range(2), repeat=4)}
        assert set(split.orbit(board, 2)) <= board_set
    fibers = Counter(board[:4] for board in boards)
    assert len(fibers) == 16
    records = []
    model = 'binary-exhaustive-cell-dfs-v1'
    for case in manifests[2]['cases']:
        prefix = case['representative']
        assert all(fibers[member] == fibers[prefix] for member in case['orbit_members'])
        records.append(split.VerifiedCount(prefix, model, 2, 5, fibers[prefix],
                       {'method': 'complete independent cell DFS',
                        'all_binary_boards_sha256': split.json_digest(sorted(boards))}))
    total = split.aggregate(manifests[2], records, model)
    assert total['full_count_decimal'] == '168'
    assert sum(record.count for record in records) == 72
    assert sum(record.count for record in records) * 4 != 168
    assert sum(fibers.values()) == 168
    expected_binary = {'0000': 24, '0001': 9, '0010': 14, '0011': 3, '0101': 2, '0111': 20}
    assert {record.prefix: record.count for record in records} == expected_binary
    for index, label in enumerate(('missing-first', 'missing-last')):
        partial = records[1:] if index == 0 else records[:-1]
        refuses(label, lambda partial=partial: split.aggregate(manifests[2], partial, model))
    refuses('duplicate-record', lambda: split.aggregate(manifests[2], records+[records[0]], model))
    refuses('no-records', lambda: split.aggregate(manifests[2], [], model))
    refuses('unaudited-dictionaries', lambda: split.aggregate(manifests[2], [record.__dict__ for record in records], model))
    for status in ('INCOMPLETE', 'BACKEND_ERROR', 'POSTPROCESS_ERROR', 'COMPLETE_FROM_LEADING_IDEAL', 'PREPARED_NOT_RUN'):
        changed = [replace(records[0], status=status)] + records[1:]
        refuses('record-status-'+status, lambda changed=changed: split.aggregate(manifests[2], changed, model))
    changes = {
        'wrong-model': dict(model='something-else'), 'wrong-palette': dict(colors=3),
        'wrong-height': dict(board_rows=10), 'wrong-prefix': dict(prefix='0'),
        'noncanonical-prefix': dict(prefix='1111'), 'negative-count': dict(count=-1),
        'float-count': dict(count=24.0), 'boolean-count': dict(count=True),
        'normalized-scope': dict(count_scope='symmetry orbits'),
        'unexpected-multiplier': dict(count_multiplier=12),
        'symmetry-normalized': dict(symmetry_normalization=True),
        'no-provenance': dict(provenance={})}
    for name, change in changes.items():
        changed = [replace(records[0], **change)] + records[1:]
        refuses(name, lambda changed=changed: split.aggregate(manifests[2], changed, model))
    for name, operation in (
            ('wrong-weight', lambda m: m['cases'][0].update(orbit_weight=12)),
            ('missing-case', lambda m: m['cases'].pop()),
            ('duplicate-case', lambda m: m['cases'].append(m['cases'][0])),
            ('wrong-members', lambda m: m['cases'][0]['orbit_members'].pop()),
            ('wrong-stabilizer', lambda m: m['cases'][0].update(stabilizer_order=1))):
        changed = deepcopy(manifests[2]); operation(changed)
        refuses('manifest-'+name, lambda changed=changed: split.aggregate(changed, records, model))
    zero = split.aggregate(manifests[2], [replace(r, count=0) for r in records], model)
    assert zero['full_count_decimal'] == '0'
    huge = split.aggregate(manifests[2], [replace(r, count=10**100) for r in records], model)
    assert huge['full_count_decimal'] == str(16*10**100)

    # Reuse completed artifacts only: this check starts no algebra process.
    example = ROOT/'experiments/exact_algebra_backend_prime29_normalized_six_check.json'
    example_data = split.read_json(example)
    valid = split.audit_backend_result(example, 'prime-all:29', example_data['prefix'])
    assert valid.count == 6
    refuses('nine-row-count-is-not-cap-count', lambda: split.aggregate(manifests[3], [valid], 'prime-all:29'))
    with tempfile.TemporaryDirectory(prefix='exact_symmetry_split_check_') as directory:
        directory = Path(directory)
        fixture = directory/'result.json'
        fixture_log = fixture.with_suffix('.log')
        original_log = example.with_suffix('.log').read_text()

        def check_altered(name, changes=None, change_log=None):
            data = deepcopy(example_data)
            if changes:
                data.update(changes)
            fixture.write_text(json.dumps(data))
            fixture_log.write_text(change_log if change_log is not None else original_log)
            refuses('artifact-'+name, lambda: split.audit_backend_result(fixture, 'prime-all:29', example_data['prefix']))

        for status in ('BACKEND_ERROR', 'INCOMPLETE_STANDARD_BASIS_TIMEOUT', 'PREPARED_NOT_RUN', 'COMPLETE_FROM_LEADING_IDEAL'):
            check_altered(status, {'status': status})
        for name, changes in {
            'basis-incomplete': {'basis_complete': False},
            'dimension-incomplete': {'dimension_complete': False},
            'leading-export-incomplete': {'leading_export_complete': False},
            'nonzero-exit': {'returncode': 1}, 'wall-timeout': {'wall_timeout_reached': True},
            'error-diagnostics': {'error_diagnostics': ['error']},
            'wrong-model': {'model': 'prime:29'}, 'wrong-prefix': {'prefix': '0000'},
            'wrong-ring': {'ring_type': 'Boolean quotient ring'},
            'wrong-free-cells': {'free_original_cells': list(range(19))},
            'wrong-variable-count': {'variables': 96},
            'wrong-prefix-rows': {'fixed_prefix_rows': 2},
            'wrong-model-hash': {'model_data_sha256': '0'*64},
            'wrong-script-hash': {'script_sha256': '0'*64},
            'count-disagreement': {'independent_monomial_dimension': 7},
            'decimal-disagreement': {'dimension_decimal': '60'},
            'wrong-scope': {'count_scope': 'full labeled boards'},
            'multiplier': {'unrestricted_multiplier': 3},
            'normalization': {'normalize_apex': True},
            'missing-leading-file': {'leading_monomials_file': str(directory/'missing.json')},
        }.items():
            check_altered(name, changes)
        check_altered('log-missing-marker', change_log=original_log.replace('GB_COMPLETE\n', ''))
        check_altered('log-error', change_log=original_log+'? error in backend\n')
        check_altered('log-duplicate-field', change_log=original_log+'HILB_DIM=6\n')
        check_altered('log-wrong-count', change_log=original_log.replace('HILB_DIM=6', 'HILB_DIM=7'))
        altered_script = directory/'changed.sing'
        altered_script.write_text(split.resolve_artifact(example_data['script']).read_text()+'\n')
        check_altered('changed-input-with-updated-hash',
                      {'script': str(altered_script), 'script_sha256': split.digest(altered_script.read_bytes())})
        altered_leading = directory/'changed.leading.json'
        leading_data = split.read_json(split.resolve_artifact(example_data['leading_monomials_file']))
        leading_data['leading_monomials'][0][0] += 1
        altered_leading.write_text(json.dumps(leading_data))
        check_altered('changed-leading-export', {'leading_monomials_file': str(altered_leading)})
        duplicate_json = directory/'duplicate.json'
        duplicate_json.write_text('{"status":"BACKEND_ERROR","status":"COMPLETE"}')
        refuses('duplicate-json-key', lambda: split.read_json(duplicate_json))

        manifest_file = directory/'manifest.json'
        manifest_file.write_text(json.dumps(manifests[3]))
        refused_file = directory/'refused.json'
        process = subprocess.run([sys.executable, str(ROOT/'experiments/exact_symmetry_split.py'),
                                  'aggregate', '--manifest', str(manifest_file),
                                  '--output', str(refused_file), str(example)],
                                 capture_output=True, text=True)
        assert process.returncode == 2
        refused = split.read_json(refused_file)
        assert refused['status'] == 'REFUSED' and refused['exact_total_available'] is False
        assert 'full_count_decimal' not in refused

    coverage = split.witness_coverage()
    assert coverage['distinct_boards'] == 1557
    covered = {case['prefix']: case['witness_boards'] for case in coverage['cases'] if case['covered']}
    assert covered == {'0000': 1519, '0001': 26, '0011': 4, '0111': 2, '0112': 6}
    for q, manifest in manifests.items():
        (ROOT/f'experiments/exact_symmetry_split_manifest_{q}.json').write_text(json.dumps(manifest, indent=2)+'\n')
    (ROOT/'experiments/exact_symmetry_split_binary_aggregate.json').write_text(json.dumps(total, indent=2)+'\n')
    (ROOT/'experiments/exact_symmetry_split_coverage.json').write_text(json.dumps(coverage, indent=2)+'\n')
    report = dict(status='PASS', independently_checked_caps=checked_caps,
                  ternary_orbits=10, ternary_orbit_weights_sum=81,
                  binary_orbits=6, binary_orbit_weights_sum=16,
                  exhaustive_binary_total=168, binary_raw_cap_counts=expected_binary,
                  binary_all_16_fibers=dict(sorted(fibers.items())),
                  binary_enumeration=enumeration_stats,
                  authoritative_completed_artifact_fixture_count=6,
                  rejection_cases=len(rejected), rejected_cases=rejected,
                  bigint_fixture_decimal=huge['full_count_decimal'],
                  witness_boards_checked=coverage['distinct_boards'],
                  ternary_complete_cap_counts_available=0,
                  ternary_search_launched=False, exact_ternary_total_available=False)
    (ROOT/'experiments/exact_symmetry_split_checks.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
