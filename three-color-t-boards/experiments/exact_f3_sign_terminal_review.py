#!/usr/bin/env python3
"""Strict terminal-only audit of the eighth-build full quintic-sign trial.

Requires existing backend and outer terminal JSONs. Starts no solver and does
not infer termination from elapsed time or from an incomplete progress log.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

from exact_msolve_backend import definitions, parse_leading
from exact_standard_monomials import count_standard_monomials
from exact_algebra_backend import monomial_dimension
from exact_sign_branch_aggregate import _check_terminal, artifact, require

HERE = Path(__file__).resolve().parent
NAME = 'exact_msolve_full_native3_sign_minfill_byte_4g'
INPUT_SHA = '14247d0e4cfaff8636e99852902816d8d0ab97de47ada08cb2e40fa7576e71cf'
MODEL_SHA = 'd8e366d5dabbc3eddfe0fdf519ea87b1f37602b153e47f209f70c2553db41bbd'
EXE_SHA = '63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def progress(log):
    rounds=[];current=None;promotions=[];symbolic=[];stages=[]
    for line in log.splitlines():
        header=re.match(r'^\s*(\d+)\s+(\d+)\s+(\d+)(?:\s+(\d+)\s+x\s+(\d+))?',line)
        if header:
            current=dict(degree=int(header[1]),selected_pairs=int(header[2]),pending_pairs_shown=int(header[3]),
                matrix_rows=int(header[4]) if header[4] else None,
                matrix_columns=int(header[5]) if header[5] else None,round_timing_printed=False)
            rounds.append(current)
        dimensions=re.match(r'^\s*(\d+)\s+x\s+(\d+)\s+',line)
        if current is not None and dimensions:
            require(current['matrix_rows'] is None,'unexpected duplicate matrix dimensions')
            current.update(matrix_rows=int(dimensions[1]),matrix_columns=int(dimensions[2]))
        if current is not None and re.match(r'^\s*\d+\.\d+\s*\|\s*\d+\.\d+\s*$',line):
            current['round_timing_printed']=True
        for prefix, rows in [('MSOLVE_PROMOTION_COLUMNS ',promotions),
                             ('MSOLVE_SYMBOLIC_CAPACITY_REQUEST ',symbolic),
                             ('MSOLVE_SYMBOLIC_STAGING ',stages)]:
            if line.startswith(prefix):rows.append({k:int(v) for k,v in re.findall(r'(\w+)=(\d+)',line)})
    completed=[r for r in rounds if r['round_timing_printed']]
    return dict(completed_rounds_with_timing=len(completed),last_completed_round=completed[-1] if completed else None,
        last_started_round=rounds[-1] if rounds else None,last_completed_promotion=promotions[-1] if promotions else None,
        symbolic_capacity_request_count=len(symbolic),last_symbolic_capacity_request=symbolic[-1] if symbolic else None,
        symbolic_staging_rounds=len(stages),raw_log_failure_diagnostics=[line for line in log.splitlines()
            if re.search(r'\berror\b|failed|out of memory|cannot allocate|segmentation|aborted',line,re.I)])


def main():
    stem=HERE/NAME
    data=json.loads(stem.with_suffix('.json').read_bytes())
    outer=json.loads(stem.with_suffix('.outer.json').read_bytes())
    preflight=json.loads(stem.with_suffix('.preflight.json').read_bytes())
    require(outer.get('status')=='OUTER_PROCESS_FINISHED' and outer.get('outer_wall_limit_reached') is False,
            'outer process has not finished normally')
    require(outer.get('backend_status')==data.get('status'),'terminal status disagreement')
    expected,metadata=definitions(prime=3,ternary_native_field=True,native_e3=True,
        native_translation=True,native_order='minimum-fill',native_sign=True)
    require(stem.with_suffix('.ms').read_text()==expected,'actual full sign input mismatch')
    require(sha(stem.with_suffix('.ms'))==data.get('source_sha256')==data.get('input_sha256')==INPUT_SHA,
            'input hash mismatch')
    for key,value in metadata.items():
        if key not in ('status','source_sha256','standard_basis_complete','sign_exporter_sha256'):
            require(data.get(key)==value and type(data.get(key)) is type(value),'model mismatch: '+key)
    require(data.get('sign_model_source_sha256')==MODEL_SHA,'unexpected source model')
    require(data.get('variables')==97 and data.get('generators')==179 and
            data.get('count_divisor')==data.get('count_multiplier')==1,'unexpected full-count scope')
    require(data.get('native_sign_branch') is None and not data.get('prefix') and
            data.get('offset_variable_index')==95 and data.get('sign_variable_index')==96,
            'branch/prefix restriction or missing independent factor')
    command=data.get('command')
    require(isinstance(command,list) and len(command)==19 and
            command[1:15]==['-g','1','-l','2','-t','1','-r','1','-c','0','-v','2','-m','16'] and
            command[15]=='-f' and artifact(command[16])==stem.with_suffix('.ms') and
            command[17]=='-o' and artifact(command[18])==stem.with_suffix('.basis'),'unexpected exact solver command')
    require(data.get('executable_sha256')==sha(artifact(command[0]))==EXE_SHA,'executable mismatch')
    libraries=data.get('local_shared_libraries');require(isinstance(libraries,dict) and libraries,'missing library hashes')
    for path,hashed in libraries.items():require(sha(artifact(path))==hashed,'local library mismatch')
    require(preflight.get('status')=='LAUNCH' and preflight.get('executable_sha256')==EXE_SHA and
            preflight.get('memory_cap_mb')==data.get('memory_mb')==4096 and
            preflight.get('available_mb')>=preflight.get('required_available_mb')==4608 and
            preflight.get('seconds')==data.get('timeout_seconds')==900,'preflight mismatch')
    require(outer.get('outer_wall_limit_seconds')==960 and outer.get('outer_memory_mb')==4096,'outer limits mismatch')
    log=stem.with_suffix('.log').read_text()
    require(data['status'] in stem.with_suffix('.outer.log').read_text(),'outer log status mismatch')
    markers=sum(line.strip()=='MSOLVE_PRIME_GB_EXPORT_COMPLETE' for line in log.splitlines())
    require(data.get('export_marker_count')==markers,'marker count mismatch')
    require('MSOLVE_F2_BITSET rows=' not in log,'unexpected F2 kernel')
    count=None
    if data['status']=='COMPLETE':
        require(outer['returncode']==0,'successful backend with failed outer wrapper')
        count=_check_terminal(data,log)
        require(data.get('standard_basis_complete') is True,'fixed backend completion flag absent')
        require(count>=45083592 and count%12==0,'full-count sanity check failed')
        require(sha(stem.with_suffix('.basis'))==data.get('basis_sha256'),'basis hash mismatch')
        leading=parse_leading(stem.with_suffix('.basis').read_text(),97,3)
        exported=json.loads(stem.with_suffix('.leading.json').read_bytes())
        require(exported==dict(format='leading-monomial-ideal-v1',variables=97,standard_basis_complete=True,
            leading_monomials=leading,provenance=dict(backend='msolve F4',input_sha256=INPUT_SHA,
                executable_sha256=EXE_SHA,field='F3',linear_algebra='exact sparse')),'leading export mismatch')
        require(data.get('basis_size')==len(leading),'basis size mismatch')
        first=count_standard_monomials(leading,97,standard_basis_complete=True,max_states=1_000_000)
        second,_=monomial_dimension(leading,97,seconds=60)
        require(first==second==count,'independent integer recount mismatch')
    else:
        require(data['status'] in ('BACKEND_ERROR','INCOMPLETE_TIMEOUT','POSTPROCESS_ERROR') and
                outer['returncode']==1,'unknown terminal failure status')
        require('dimension_decimal' not in data and 'board_count_decimal' not in data,'count on incomplete run')
        if data['status']!='POSTPROCESS_ERROR':
            require(data.get('basis_complete') is False and markers==0 and
                    stem.with_suffix('.basis').stat().st_size==0 and not stem.with_suffix('.leading.json').exists(),
                    'unexpected partial export on failed run')
    record=dict(name=NAME,status=data['status'],basis_complete=data['basis_complete'],count_complete=count is not None,
        quotient_dimension_decimal=str(count) if count is not None else None,
        full_labeled_board_count_decimal=str(count) if count is not None else None,count_scope='full labeled boards',
        variables=97,coupled_variables=95,generators=179,prime=3,field='F3',count_divisor=1,count_multiplier=1,
        independent_offset_index=95,independent_sign_index=96,both_independent_factors_retained=True,
        input_sha256=INPUT_SHA,sign_model_source_sha256=MODEL_SHA,executable_sha256=EXE_SHA,
        adapter_sha256=data.get('adapter_sha256'),solver_cpu_seconds=data['child_cpu_seconds'],
        solver_wall_seconds=data['child_wall_seconds'],solver_wall_limit_seconds=data['timeout_seconds'],
        memory_mb=data['memory_mb'],solver_returncode=data.get('returncode'),outer_returncode=outer['returncode'],
        outer_wall_seconds=outer['elapsed_seconds'],process_tree_cpu_seconds=outer['process_tree_cpu_seconds'],
        outer_wall_limit_reached=False,export_marker_count=markers,basis_file_bytes=stem.with_suffix('.basis').stat().st_size,
        leading_export_present=stem.with_suffix('.leading.json').exists(),preflight=preflight,
        backend_error_diagnostics=data['error_diagnostics'],solver_processes_started_by_this_audit=0,
        artifact_sha256={suffix:sha(stem.with_suffix(suffix)) for suffix in
            ('.json','.outer.json','.log','.outer.log','.ms','.basis','.preflight.json')},**progress(log))
    if data.get('returncode')==-11:
        record.update(termination_signal='SIGSEGV',underlying_failure_cause='Not established from a capacity request alone.')
    report=dict(status='CHECKED_TERMINAL_ARTIFACTS',audited_at_utc=datetime.now(timezone.utc).isoformat(),record=record,
        semantics='Only normal completed exact basis export plus two integer recounts supplies a count.')
    (HERE/'exact_f3_sign_terminal_review_results.json').write_text(json.dumps(report,indent=2)+'\n')
    aggregate_path=HERE/'exact_msolve_current_trials_audit.json';aggregate=json.loads(aggregate_path.read_bytes())
    aggregate['trials']=[r for r in aggregate['trials'] if r['name']!=NAME]+[record]
    aggregate.update(last_audited_at_utc=report['audited_at_utc'],latest_audited_trials=[NAME],
        unrestricted_count=str(count) if count is not None else None,
        status='CHECKED_FULL_COUNT' if count is not None else 'CHECKED_NO_FULL_COUNT',
        terminal_semantics=report['semantics'],solver_processes_started_by_this_audit=0)
    aggregate_path.write_text(json.dumps(aggregate,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k!='artifact_sha256'},indent=2))


if __name__=='__main__':main()
