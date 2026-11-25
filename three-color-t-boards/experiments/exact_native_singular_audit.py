#!/usr/bin/env python3
"""Read-only audit of the four preserved native-F3 Singular trials."""
import copy
import hashlib
import json
from pathlib import Path

import exact_native_singular as adapter

HERE = Path(__file__).resolve().parent


def main():
    for case in adapter.INPUTS:
        definition, metadata = adapter.definition(case)
        original = (HERE/adapter.INPUTS[case][0]).read_text().split('\n', 2)[2].strip()
        assert definition.split('ideal I=', 1)[1][:-2] == original
        assert metadata['prime'] == 3 and metadata['variables'] == 96
        assert metadata['count_divisor'] == metadata['count_multiplier'] == 1
    fixtures = []
    for algorithm in ['std', 'slimgb']:
        stem = HERE/('exact_native_singular_six_'+algorithm)
        result = json.loads(stem.with_suffix('.json').read_text())
        log = stem.with_suffix('.log').read_text()
        adapter.strict_completion(result, log, 'six')
        leading = json.loads(stem.with_suffix('.leading.json').read_text())
        from_log = [list(map(int, line[3:].split(','))) for line in log.splitlines()
                    if line.startswith('LM=')]
        assert leading['leading_monomials'] == from_log
        assert result['script_sha256'] == hashlib.sha256(stem.with_suffix('.sing').read_bytes()).hexdigest()
        fixtures.append(dict(algorithm=algorithm, count=6, basis_size=len(from_log)))
    bad = []
    for marker in ['GB_STARTED', 'GB_COMPLETE', 'LM_COMPLETE', 'HILB_STARTED', 'BACKEND_COMPLETE']:
        bad += [(result, log.replace(marker, 'REMOVED', 1)), (result, log+'\n'+marker+'\n')]
    for key, value in [('returncode', 1), ('wall_timeout_reached', True),
                       ('basis_complete', False), ('standard_basis_complete', False),
                       ('leading_export_complete', False), ('dimension_complete', False),
                       ('monomial_dimension', 7), ('independent_monomial_dimension', 7),
                       ('hilbert_dimension', 7)]:
        changed = copy.deepcopy(result)
        changed[key] = value
        bad.append((changed, log))
    for field in ['BASIS_IS_STANDARD', 'KRULL_DIM', 'BASIS_SIZE', 'HILB_TYPE', 'HILB_DIM']:
        line = next(line for line in log.splitlines() if line.startswith(field+'='))
        bad.append((result, log+'\n'+line+'\n'))
    for result, log in bad:
        try:
            adapter.strict_completion(result, log, 'six')
        except ValueError:
            pass
        else:
            raise AssertionError('malformed completion accepted')
    terminal = []
    for algorithm in ['std', 'slimgb']:
        stem = HERE/('exact_native_singular_full_'+algorithm+'_3g')
        result = json.loads(stem.with_suffix('.json').read_text())
        log = stem.with_suffix('.log').read_text()
        assert result['status'] == 'BACKEND_ERROR' and result['returncode'] == 14
        assert not any(result[k] for k in ['basis_complete', 'dimension_complete',
                                          'leading_export_complete', 'wall_timeout_reached'])
        assert 'GB_COMPLETE' not in log and 'Singular error: no more memory' in log
        assert not stem.with_suffix('.leading.json').exists()
        assert result['input_sha256'] == adapter.INPUTS['minimum-fill'][1]
        terminal.append(dict(algorithm=algorithm, status=result['status'], count=None,
                             child_cpu_seconds=result['child_cpu_seconds'],
                             elapsed_seconds=result['elapsed_seconds']))
    report = dict(status='PASS', frozen_definition_roundtrips=2,
                  completed_fixtures=fixtures, strict_completion_rejections=len(bad),
                  terminal_unrestricted_trials=terminal,
                  adapter_sha256=hashlib.sha256(Path(adapter.__file__).read_bytes()).hexdigest())
    (HERE/'exact_native_singular_adapter_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
