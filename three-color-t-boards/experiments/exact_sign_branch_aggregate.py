#!/usr/bin/env python3
"""Audit and sum exactly four complete, unrestricted linear-sign branches.

Only the sixteen frozen uneliminated/affine-eliminated inputs are accepted.
Both variable orders and elimination forms are alternatives, never summands.
No solver is run. Missing/error/timeout results are unknown and never zero.
"""
import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re

from exact_msolve_backend import parse_leading
from exact_msolve_native_sign_branch import branch_definitions
from exact_msolve_native_branch_elimination import eliminated_branch_definitions
from exact_standard_monomials import count_standard_monomials
from exact_algebra_backend import monomial_dimension

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MANIFEST_SHA = '9ecb49f828699a3966c0349bddb4bc4f57cc163b65ba1855770357bf2e39d2c7'
ELIMINATION_MANIFEST_SHA = '91e25ac8803be65a12998e344060e3e48778e499722f30aaf7b5a663f8b2eaa0'
REVIEWED_EXECUTABLES = {
    'a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a',
    '63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76',
}
MARKER = 'MSOLVE_PRIME_GB_EXPORT_COMPLETE'
ERROR = re.compile(r'\berror\b|failed|out of memory|cannot allocate|segmentation|aborted', re.I)
LOWER_BOUND = 45083592


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def artifact(path):
    path = Path(path)
    return (path if path.is_absolute() else ROOT / path).resolve()


def decimal(value, name):
    require(isinstance(value, str) and re.fullmatch(r'0|[1-9][0-9]*', value),
            f'invalid nonnegative integer decimal: {name}')
    return int(value)


def _check_scope(data, raw_input):
    """Check exact frozen input and all model metadata, independently of status."""
    branch = data.get('native_sign_branch')
    require(type(branch) is int and branch in range(4), 'invalid branch ID')
    order = data.get('native_variable_order')
    require(order in ('natural', 'minimum-fill'), 'unsupported branch variable order')
    eliminated = data.get('native_branch_elimination', False)
    require(type(eliminated) is bool, 'invalid elimination selector')
    require(data.get('native_affine_elimination', False) is eliminated,
            'inconsistent affine-elimination metadata')
    exporter = eliminated_branch_definitions if eliminated else branch_definitions
    expected, model = exporter(branch, None if order == 'natural' else order)
    require(digest((HERE / 'exact_f3_sign_branches_manifest.json').read_bytes()) == MANIFEST_SHA,
            'unreviewed branch manifest')
    if eliminated:
        elimination_raw = (HERE / 'exact_f3_branch_elimination_manifest.json').read_bytes()
        require(digest(elimination_raw) == ELIMINATION_MANIFEST_SHA, 'unreviewed elimination manifest')
        require(json.loads(elimination_raw)['source_manifest_sha256'] == MANIFEST_SHA,
                'elimination manifest has a different source partition')
    require(raw_input == expected.encode('ascii'), 'actual input is not a frozen full branch input')
    require(data.get('source_sha256') == data.get('input_sha256') == digest(raw_input),
            'input hash mismatch')
    header, prime, body = raw_input.decode('ascii').split('\n', 2)
    variables, generators = (96-branch, 177-branch) if eliminated else (97, 179+branch)
    require(header == ','.join(f'x{i+1}' for i in range(variables)) and prime == '3',
            'branch ring header mismatch')
    require(len(body.strip().split(',\n')) == generators, 'branch generator count mismatch')
    # These fields change after preparation or are provenance of the adapter,
    # rather than the frozen mathematical model. Completion is checked below.
    skipped = {'status', 'standard_basis_complete', 'source_sha256', 'branch_exporter_sha256'}
    for key, value in model.items():
        if key not in skipped:
            require(data.get(key) == value and type(data.get(key)) is type(value),
                    f'branch model metadata mismatch: {key}')
    for key in ('binary', 'fixture', 'pivot_order', 'dispersed_variable_order',
                'normalize_apex', 'palette_canonical', 'orbit_canonical',
                'ternary_reduced', 'ternary_prefix_sums', 'histogram_e2', 'histogram_e4',
                'affine_eliminated', 'mock_test_only'):
        require(not data.get(key), f'unsupported restriction or synthetic record: {key}')
    require(data.get('count_divisor') == data.get('count_multiplier') == 1,
            'unexpected external factor')
    require(not data.get('unrestricted_multiplier', 0), 'unexpected unrestricted multiplier')
    return branch, order


def _check_terminal(data, log):
    require(data.get('status') == 'COMPLETE', 'branch result is not COMPLETE')
    require(type(data.get('returncode')) is int and data['returncode'] == 0,
            'solver did not exit normally')
    require(data.get('basis_complete') is True, 'basis is incomplete')
    for key in ('standard_basis_complete', 'leading_export_complete', 'dimension_complete'):
        if key in data:
            require(data[key] is True, f'contradictory completion flag: {key}')
    require(data.get('require_export_marker') is True and
            type(data.get('export_marker_count')) is int and data['export_marker_count'] == 1,
            'completion attestation not required or not unique')
    require(data.get('error_diagnostics') == [] and not data.get('postprocess_error'),
            'backend diagnostics present')
    require(sum(line.strip() == MARKER for line in log.splitlines()) == 1,
            'actual log marker missing or duplicated')
    require(not ERROR.search(log), 'actual solver log contains failure diagnostic')
    require(data.get('linear_algebra') == 'exact sparse (-l 2)' and
            type(data.get('threads')) is int and data['threads'] == 1,
            'unsupported arithmetic mode')
    dimension = decimal(data.get('dimension_decimal'), 'quotient dimension')
    count = decimal(data.get('board_count_decimal'), 'branch board count')
    require(dimension == count and count % 6 == 0, 'branch dimension/factor-six sanity mismatch')
    return count


@dataclass(frozen=True)
class _AuditedBranch:
    branch: int
    order: str
    eliminated: bool
    count: int
    evidence: dict


def _check_runtime_artifacts(data, path):
    """Check the actual exact-mode command, executable, libraries and log path."""
    input_path = path.with_suffix('.ms')
    log_path, basis_path = path.with_suffix('.log'), path.with_suffix('.basis')
    require(artifact(data.get('input_file', '')) == input_path, 'input path mismatch')
    require(artifact(data.get('log_file', '')) == log_path, 'log path mismatch')
    command = data.get('command')
    require(isinstance(command, list) and len(command) == 19 and all(isinstance(x, str) for x in command),
            'unexpected solver command')
    require(command[1:13] == ['-g','1','-l','2','-t','1','-r','1','-c','0','-v','2'] and
            command[13] == '-m' and re.fullmatch(r'0|[1-9][0-9]*', command[14]) and
            command[15] == '-f' and artifact(command[16]) == input_path and
            command[17] == '-o' and artifact(command[18]) == basis_path,
            'command does not use the exact input/export mode')
    exe_hash = data.get('executable_sha256')
    require(exe_hash in REVIEWED_EXECUTABLES and digest(artifact(command[0]).read_bytes()) == exe_hash,
            'unreviewed or changed executable')
    libraries = data.get('local_shared_libraries')
    require(isinstance(libraries, dict) and libraries, 'missing library provenance')
    for name, value in libraries.items():
        require(digest(artifact(name).read_bytes()) == value, 'changed local shared library')
    raw_log = log_path.read_bytes()
    return raw_log, exe_hash


def audit_branch_result(result_path, *, max_states=1_000_000, counter_seconds=60):
    """Read authoritative artifacts and independently recount a completed basis."""
    path = artifact(result_path)
    raw_result = path.read_bytes()
    data = json.loads(raw_result)
    require(isinstance(data, dict) and not data.get('mock_test_only'), 'synthetic or invalid result')
    require(data.get('status') == 'COMPLETE', 'branch result is not COMPLETE')
    branch, order = _check_scope(data, path.with_suffix('.ms').read_bytes())
    variables = data['variables']
    basis_path = path.with_suffix('.basis')
    raw_log, exe_hash = _check_runtime_artifacts(data, path)
    count = _check_terminal(data, raw_log.decode('utf-8'))
    # An enclosing process is optional; if present it must corroborate a normal
    # completed return and may not attest a timeout/error instead.
    outer_path = path.with_suffix('.outer.json')
    if outer_path.exists():
        outer = json.loads(outer_path.read_bytes())
        require(outer.get('status') == 'OUTER_PROCESS_FINISHED' and
                outer.get('returncode') == 0 and outer.get('backend_status') == 'COMPLETE' and
                outer.get('outer_wall_limit_reached') is False, 'outer process did not finish successfully')
    raw_basis = basis_path.read_bytes()
    require(digest(raw_basis) == data.get('basis_sha256'), 'basis hash mismatch')
    leading = parse_leading(raw_basis.decode('ascii'), variables, 3)
    require(type(data.get('basis_size')) is int and data['basis_size'] == len(leading), 'basis size mismatch')
    export_path = path.with_suffix('.leading.json')
    raw_export = export_path.read_bytes()
    expected_export = dict(format='leading-monomial-ideal-v1', variables=variables,
        standard_basis_complete=True, leading_monomials=leading,
        provenance=dict(backend='msolve F4', input_sha256=data['source_sha256'],
                        executable_sha256=exe_hash, field='F3', linear_algebra='exact sparse'))
    require(json.loads(raw_export) == expected_export, 'leading export or provenance mismatch')
    first = count_standard_monomials(leading, variables, standard_basis_complete=True, max_states=max_states)
    second, _ = monomial_dimension(leading, variables, seconds=counter_seconds)
    require(first == second == count, 'independent exact leading-ideal recounts disagree')
    return _AuditedBranch(branch, order, data.get('native_branch_elimination', False), count, dict(
        result=str(path), result_sha256=digest(raw_result), input_sha256=data['source_sha256'],
        branch_model_source_sha256=data['branch_model_source_sha256'],
        branch_manifest_sha256=data['branch_manifest_sha256'], executable_sha256=exe_hash,
        variables=variables, generators=data['generators'],
        log_sha256=digest(raw_log), basis_sha256=digest(raw_basis), leading_sha256=digest(raw_export),
        quotient_dimension_decimal=str(count), normal_exit_verified=True,
        unique_actual_export_marker=True, completed_basis_recounted_by_two_integer_algorithms=True))


def audit_branch_terminal(result_path, *, max_states=1_000_000, counter_seconds=60):
    """Audit one terminal branch, preserving unknown counts on incomplete runs.

    Unlike aggregation this reports process and scope evidence even for a
    timeout/error. It never supplies a full-board total or a substitute zero.
    """
    path=artifact(result_path);raw=path.read_bytes();data=json.loads(raw)
    require(isinstance(data,dict) and not data.get('mock_test_only'),'synthetic or invalid result')
    require(data.get('status') in ('COMPLETE','BACKEND_ERROR','INCOMPLETE_TIMEOUT','POSTPROCESS_ERROR'),
            'branch does not have a terminal status')
    branch,order=_check_scope(data,path.with_suffix('.ms').read_bytes())
    raw_log,exe_hash=_check_runtime_artifacts(data,path);log=raw_log.decode('utf-8')
    outer_path=path.with_suffix('.outer.json');outer=json.loads(outer_path.read_bytes())
    require(outer.get('status')=='OUTER_PROCESS_FINISHED' and
            outer.get('outer_wall_limit_reached') is False and outer.get('backend_status')==data['status'],
            'outer process is not terminal or disagrees with backend')
    require(type(outer.get('returncode')) is int and outer['returncode']==(0 if data['status']=='COMPLETE' else 1),
            'outer return code mismatch')
    markers=sum(line.strip()==MARKER for line in log.splitlines())
    require(data.get('export_marker_count')==markers,'actual marker count mismatch')
    count=None;evidence=None
    if data['status']=='COMPLETE':
        verified=audit_branch_result(path,max_states=max_states,counter_seconds=counter_seconds)
        require(verified.evidence['result_sha256']==digest(raw),'terminal result changed during audit')
        count=verified.count;evidence=verified.evidence
    else:
        require('dimension_decimal' not in data and 'board_count_decimal' not in data,
                'count present on incomplete result')
        if data['status']=='INCOMPLETE_TIMEOUT':
            require(data.get('returncode') is None,'timeout has a claimed normal solver return')
        else:
            require(type(data.get('returncode')) is int,'missing terminal solver return code')
        if data['status']!='POSTPROCESS_ERROR':
            require(data.get('basis_complete') is False and markers==0 and
                    path.with_suffix('.basis').stat().st_size==0 and not path.with_suffix('.leading.json').exists(),
                    'unexpected partial export on failed run')
    preflight_path=path.with_suffix('.preflight.json');preflight=json.loads(preflight_path.read_bytes())
    require(preflight.get('status')=='LAUNCH' and preflight.get('memory_cap_mb')==data.get('memory_mb') and
            preflight.get('seconds')==data.get('timeout_seconds') and
            preflight.get('executable_sha256')==exe_hash and
            preflight.get('required_available_mb')==data['memory_mb']+512 and
            preflight.get('available_mb')>=preflight['required_available_mb'],'branch preflight mismatch')
    from exact_f3_sign_terminal_review import progress
    record=dict(name=path.stem,status=data['status'],branch_id=branch,order=order,
        affine_eliminated=data.get('native_branch_elimination',False),count_scope=data['count_scope'],
        variables=data['variables'],generators=data['generators'],prime=3,field='F3',
        count_divisor=1,count_multiplier=1,offset_variable_index=data['offset_variable_index'],
        sign_variable_index=data['sign_variable_index'],basis_complete=data['basis_complete'],
        count_complete=count is not None,branch_count_decimal=str(count) if count is not None else None,
        full_labeled_board_count_decimal=None,full_total_requires_branch_ids=[0,1,2,3],
        input_sha256=data['source_sha256'],branch_model_source_sha256=data['branch_model_source_sha256'],
        branch_manifest_sha256=data['branch_manifest_sha256'],executable_sha256=exe_hash,
        solver_cpu_seconds=data['child_cpu_seconds'],solver_wall_seconds=data['child_wall_seconds'],
        solver_wall_limit_seconds=data['timeout_seconds'],memory_mb=data['memory_mb'],
        solver_returncode=data.get('returncode'),outer_returncode=outer['returncode'],
        outer_wall_seconds=outer['elapsed_seconds'],process_tree_cpu_seconds=outer['process_tree_cpu_seconds'],
        export_marker_count=markers,basis_file_bytes=path.with_suffix('.basis').stat().st_size,
        leading_export_present=path.with_suffix('.leading.json').exists(),preflight=preflight,
        backend_error_diagnostics=data['error_diagnostics'],completed_count_evidence=evidence,
        artifact_sha256={suffix:digest(path.with_suffix(suffix).read_bytes()) for suffix in
            ('.json','.ms','.log','.basis','.outer.json','.preflight.json')},**progress(log))
    if data.get('returncode')==-11:
        record.update(termination_signal='SIGSEGV',underlying_failure_cause='Not established from a capacity request alone.')
    return dict(status='CHECKED_TERMINAL_BRANCH',record=record,full_labeled_board_count_decimal=None,
                solver_processes_started=0)


def _sum_branch_counts(pairs):
    """Pure arithmetic gate; tests may exercise it with explicitly mock numbers."""
    seen = {}
    for branch, count in pairs:
        require(type(branch) is int and branch in range(4), 'invalid branch ID')
        require(branch not in seen, 'duplicate branch (including alternative ordering)')
        require(type(count) is int and count >= 0 and count % 6 == 0, 'invalid branch count')
        seen[branch] = count
    require(set(seen) == set(range(4)), 'missing branch; its count remains unknown')
    total = sum(seen.values())
    require(total >= LOWER_BOUND, 'sum contradicts certified lower bound')
    require(total % 12 == 0, 'sum contradicts free palette/reflection action')
    return total


def aggregate_results(paths, *, max_states=1_000_000, counter_seconds=60):
    paths = list(paths)
    require(len(paths) == 4, 'exactly one complete result for each of four branches is required')
    # Check IDs first, so two alternative orderings never trigger two expensive
    # recounts or get silently selected/deduplicated.
    data = [json.loads(artifact(path).read_bytes()) for path in paths]
    require(all(isinstance(row,dict) for row in data),'invalid result objects')
    ids = [row.get('native_sign_branch') for row in data]
    require(all(type(k) is int for k in ids) and sorted(ids) == [0, 1, 2, 3],
            'missing or duplicate branch IDs; ordering/elimination variants are alternatives')
    rows = [audit_branch_result(path, max_states=max_states, counter_seconds=counter_seconds) for path in paths]
    total = _sum_branch_counts((row.branch, row.count) for row in rows)
    return dict(status='COMPLETE_FOUR_BRANCH_TOTAL', count_scope='all full labeled valid ternary boards',
                full_labeled_board_count_decimal=str(total), count_divisor=1, count_multiplier=1,
                branch_manifest_sha256=MANIFEST_SHA, required_branch_ids=[0,1,2,3],
                supported_representation_manifests=[MANIFEST_SHA, ELIMINATION_MANIFEST_SHA],
                sanity_lower_bound=LOWER_BOUND, sanity_divisible_by=12,
                branches=[dict(branch_id=r.branch, order=r.order, affine_eliminated=r.eliminated,
                               count_decimal=str(r.count), evidence=r.evidence)
                          for r in sorted(rows, key=lambda r:r.branch)], solver_processes_started=0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('results', nargs='*', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--terminal', action='store_true', help='audit one terminal branch without aggregating a total')
    args = parser.parse_args()
    if args.output and args.output.exists():
        parser.error('refusing to overwrite an existing audit artifact')
    try:
        if args.terminal:
            require(len(args.results)==1,'one terminal branch result path is required')
            result=audit_branch_terminal(args.results[0])
        else:
            result = aggregate_results(args.results)
        code = 0
    except (ValueError, OSError, KeyError, TypeError, RuntimeError, MemoryError, RecursionError) as error:
        result = dict(status='INCOMPLETE_OR_INVALID', error=f'{type(error).__name__}: {error}',
                      full_labeled_board_count_decimal=None, solver_processes_started=0)
        code = 1
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        with args.output.open('x') as output:
            output.write(text)
    print(text, end='')
    raise SystemExit(code)


if __name__ == '__main__':
    main()
