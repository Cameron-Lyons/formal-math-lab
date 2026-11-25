#!/usr/bin/env python3
"""Consolidate retained terminal artifacts without launching any process."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
NAMES = (
    'exact_msolve_cap0000_prime2',
    'exact_msolve_full_prime29_pivot_rounded',
    'exact_msolve_full_prime2_bitset',
    'exact_msolve_full_prime2_elementary',
    'exact_msolve_full_prime2_prefix_gray_3g',
    'exact_msolve_full_prime2_prefix_gray_e4_3g',
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(name):
    stem = HERE/name
    result_path = stem.with_suffix('.json')
    outer_path = stem.with_suffix('.outer.json')
    result = json.loads(result_path.read_text())
    outer = json.loads(outer_path.read_text())
    log_path = stem.with_suffix('.log')
    log = log_path.read_text()
    outer_log = stem.with_suffix('.outer.log')
    assert result['status'] in ('BACKEND_ERROR','INCOMPLETE_TIMEOUT')
    assert result['basis_complete'] is False and result['export_marker_count'] == 0
    assert 'dimension_decimal' not in result and 'board_count_decimal' not in result
    assert 'quotient_dimension' not in result
    assert result.get('standard_basis_complete',False) is False
    assert outer['status'] == 'OUTER_PROCESS_FINISHED'
    assert outer['backend_status'] == result['status'] and outer['returncode'] == 1
    assert outer['outer_wall_limit_reached'] is False
    assert result['status'] in outer_log.read_text()
    assert sha(stem.with_suffix('.ms')) == result['source_sha256']
    assert sha(Path(result['command'][0])) == result['executable_sha256']
    assert stem.with_suffix('.basis').stat().st_size == 0
    assert not stem.with_suffix('.leading.json').exists()
    assert not any(line.strip() == 'MSOLVE_PRIME_GB_EXPORT_COMPLETE' for line in log.splitlines())
    headers = []
    current = None
    for line in log.splitlines():
        match = re.match(r'^\s*(\d+)\s+(\d+)\s+(\d+)(?:\s+(\d+)\s+x\s+(\d+))?',line)
        if match:
            current = dict(degree=int(match[1]),selected_pairs=int(match[2]),
                pending_pairs_shown=int(match[3]),
                matrix_rows=int(match[4]) if match[4] else None,
                matrix_columns=int(match[5]) if match[5] else None,
                round_timing_printed=False)
            headers.append(current)
        if current is not None and re.match(r'^\s*\d+\.\d+\s*\|\s*\d+\.\d+\s*$',line):
            current['round_timing_printed'] = True
    completed = [row for row in headers if row['round_timing_printed']]
    diagnostics = [line for line in log.splitlines()
                   if re.search(r'error|failed|out of memory|segmentation|aborted',line,re.I)]
    observations = {
        NAMES[0]: 'Wall timeout after a completed degree-four round; next selection header has no matrix dimensions.',
        NAMES[1]: 'Signal11 after a degree-four selection header; no dimensions or specific failure diagnostic for that round.',
        NAMES[2]: 'Explicit checked F2 bitset allocation failure in the next degree-four matrix; exit1, not a signal.',
        NAMES[3]: 'Signal11 after a degree-four selection header; no dimensions or specific failure diagnostic for that round.',
        NAMES[4]: 'Checked promotion exponent allocation failure after degree-five linear algebra; exit1 before basis export.',
        NAMES[5]: 'Hash-table exponent-vector enlargement explicitly failed for8388608 entries after the next degree-five selection; signal11 before matrix dimensions/export.',
    }
    details = dict(name=name,status=result['status'],basis_complete=False,count_complete=False,
        count_scope=result['scope'],prefix=result['prefix'],prime=result['prime'],
        variables=result['variables'],generators=result['generators'],
        count_divisor=result['count_divisor'],
        count_multiplier=result.get('count_multiplier',1),
        solver_cpu_seconds=result['child_cpu_seconds'],
        solver_wall_seconds=result['child_wall_seconds'],
        solver_wall_limit_seconds=result['timeout_seconds'],memory_mb=result['memory_mb'],
        solver_returncode=result.get('returncode'),
        solver_returncode_recorded='returncode' in result,
        outer_status=outer['status'],outer_returncode=outer['returncode'],
        outer_wall_limit_reached=outer['outer_wall_limit_reached'],
        outer_wall_seconds=outer['elapsed_seconds'],
        process_tree_cpu_seconds=outer['process_tree_cpu_seconds'],
        input_sha256=result['source_sha256'],executable_sha256=result['executable_sha256'],
        adapter_sha256=result.get('adapter_sha256'),
        histogram_e2=result.get('histogram_e2',False),
        basis_file_bytes=0,leading_export_present=False,export_marker_count=0,
        completed_rounds_with_timing=len(completed),
        last_completed_round=completed[-1] if completed else None,
        last_started_round=headers[-1] if headers else None,
        raw_log_failure_diagnostics=diagnostics,
        backend_error_diagnostics=result['error_diagnostics'],
        observed_termination=observations[name],
        artifact_sha256={suffix:sha(stem.with_suffix(suffix))
                         for suffix in ('.json','.outer.json','.log','.outer.log','.ms','.basis')})
    if name in NAMES[4:]:
        from exact_msolve_backend import definitions
        expected, metadata = definitions(prime=2,ternary_prefix_sums='all',histogram_e2=True,
            prefix_field_equations=True,histogram_e4=name==NAMES[5])
        assert stem.with_suffix('.ms').read_text() == expected
        assert result['count_divisor'] == result['count_multiplier'] == 1
        assert result['prefix'] == '' and result['symmetry_normalization'] is False
        assert result['prefix_model_source_sha256'] == metadata['prefix_model_source_sha256']
        assert result['variables'] == 96 and result['generators'] == (280 if name==NAMES[5] else 276)
        details.update(ternary_prefix_sums=True,prefix_field_equations=True,
            transformed_original_cubic_domains=100,elementary_generators=8,
            optional_prefix_field_equations=96,actual_input_matches_independent_audit=True,
            prefix_model_source_sha256=result['prefix_model_source_sha256'])
    if name == NAMES[4]:
        details.update(failed_promotion=dict(basis_load=1462002,missing=3463587,required_with_spare=4925590,
                exponent_old=1572864,exponent_new=4980736,buckets_old=4194304,buckets_new=16777216),
            last_linear_algebra_output=dict(new_rows=9,output_terms=5528411))
        assert 'missing=3463587 basis_load=1462002 basis_capacity=1572864' in log
        assert 'required_with_spare=4925590 exponent_old=1572864 exponent_new=4980736' in log
        assert 'Error: cannot allocate promotion exponent data.' in log
    if name == NAMES[5]:
        assert result['histogram_e4'] is True and result['elementary_e4_generators']==4
        assert result['pre_e4_input_sha256']=='60a5280098df62e0607fd3762a6e501b2d6098609b772138bd08f4f7ef867311'
        assert 'Enlarging exponent vector for hash table failed' in log
        assert 'for esz = 8388608, segmentation fault will follow.' in log
        details.update(histogram_e4=True,elementary_e4_generators=4,
            pre_e4_input_sha256=result['pre_e4_input_sha256'],
            failed_hash_enlargement=dict(requested_entries=8388608,
                diagnostic='Enlarging exponent vector for hash table failed; segmentation fault will follow',
                specific_hash_table_not_identified_by_this_log=True))
    return details


def main():
    records = [audit(name) for name in NAMES]
    path = HERE/'exact_msolve_current_trials_audit.json'
    document = json.loads(path.read_text())
    previous = document['trials']
    indexed = {record['name']:record for record in records}
    retained = [record for record in previous if record['name'] not in indexed]
    document.update(status='CHECKED_NO_FULL_COUNT',trials=retained+records,
        unrestricted_count=None,last_audited_at_utc=datetime.now(timezone.utc).isoformat(),
        latest_audited_trials=list(NAMES),
        terminal_semantics='No completed basis/leading export/count for any latest audited trial; failures and timeouts are not zero counts.',
        cpu_semantics='solver_cpu_seconds is child user+system CPU; solver_wall_seconds is elapsed child wall; process_tree_cpu_seconds is the outer wrapper total.',
        solver_processes_started_by_this_audit=0)
    path.write_text(json.dumps(document,indent=2)+'\n')
    for record in records:
        print(json.dumps({key:record[key] for key in ('name','status','solver_cpu_seconds',
            'solver_wall_seconds','solver_returncode','completed_rounds_with_timing',
            'last_completed_round','last_started_round','observed_termination')}))


if __name__ == '__main__':
    main()
