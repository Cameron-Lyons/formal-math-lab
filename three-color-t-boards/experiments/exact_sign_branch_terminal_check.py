#!/usr/bin/env python3
"""Simulated incomplete-terminal gate tests; no solver and no certified counts."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

import exact_sign_branch_aggregate as audit
from exact_msolve_native_branch_elimination import eliminated_branch_definitions

HERE=Path(__file__).resolve().parent


def main():
    checks=[]
    text,model=eliminated_branch_definitions(3,'minimum-fill')
    model['source_sha256']=audit.digest(text.encode())
    exe='63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76'
    base=dict(model,status='INCOMPLETE_TIMEOUT',basis_complete=False,export_marker_count=0,
        child_cpu_seconds=2.0,child_wall_seconds=3.0,timeout_seconds=900,memory_mb=3072,
        error_diagnostics=['missing or duplicate patched export-completion marker'])
    outer=dict(status='OUTER_PROCESS_FINISHED',outer_wall_limit_reached=False,backend_status='INCOMPLETE_TIMEOUT',
        returncode=1,elapsed_seconds=4.0,process_tree_cpu_seconds=2.1)
    preflight=dict(status='LAUNCH',executable_sha256=exe,memory_cap_mb=3072,seconds=900,
        available_mb=4499,required_available_mb=3584)
    # Workspace-local temporary files avoid /tmp quota and disappear afterward.
    with tempfile.TemporaryDirectory(prefix='exact-terminal-mock-',dir=HERE) as folder:
        stem=Path(folder)/'synthetic-incomplete-branch';path=stem.with_suffix('.json')
        stem.with_suffix('.ms').write_text(text);stem.with_suffix('.basis').write_text('')
        stem.with_suffix('.log').write_text('explicit synthetic terminal unit test\n')
        def write(data=base,process=outer,flight=preflight):
            path.write_text(json.dumps(data));stem.with_suffix('.outer.json').write_text(json.dumps(process))
            stem.with_suffix('.preflight.json').write_text(json.dumps(flight))
        def reject(name,data=base,process=outer,flight=preflight):
            write(data,process,flight)
            try:audit.audit_branch_terminal(path)
            except (ValueError,KeyError,TypeError,OSError):checks.append(dict(name=name,expected='reject',passed=True))
            else:raise AssertionError(name)
        with patch.object(audit,'_check_runtime_artifacts',return_value=(stem.with_suffix('.log').read_bytes(),exe)):
            for status,returncode in [('INCOMPLETE_TIMEOUT',None),('BACKEND_ERROR',-11),('POSTPROCESS_ERROR',0)]:
                data=deepcopy(base);data['status']=status
                if returncode is not None:data['returncode']=returncode
                process=dict(outer,backend_status=status);write(data,process)
                report=audit.audit_branch_terminal(path)
                assert report['status']=='CHECKED_TERMINAL_BRANCH'
                assert report['record']['branch_id']==3 and report['record']['variables']==93
                assert report['record']['generators']==174 and report['record']['memory_mb']==3072
                assert report['record']['branch_count_decimal'] is None and report['full_labeled_board_count_decimal'] is None
                checks.append(dict(name='mock-'+status,expected='terminal-only; both counts null',passed=True))
            for key,value in [('status','PREPARED_NOT_RUN'),('status','RUNNING'),('dimension_decimal','0'),
                ('board_count_decimal','0'),('returncode',0),('basis_complete',True),('export_marker_count',1),
                ('mock_test_only',True),('variables',97),('count_divisor',6),('native_sign_branch',2)]:
                bad=deepcopy(base);bad[key]=value;reject('metadata-'+key+'-'+str(value),data=bad)
            for key,value in [('status','RUNNING'),('outer_wall_limit_reached',True),('backend_status','COMPLETE'),('returncode',0)]:
                bad=deepcopy(outer);bad[key]=value;reject('outer-'+key,process=bad)
            for key,value in [('status','DEFERRED'),('memory_cap_mb',4096),('required_available_mb',4608),
                              ('available_mb',3000),('executable_sha256','0'*64),('seconds',180)]:
                bad=deepcopy(preflight);bad[key]=value;reject('preflight-'+key,flight=bad)
            write();stem.with_suffix('.basis').write_text('partial export')
            reject('partial-basis-is-not-zero');stem.with_suffix('.basis').write_text('')
            stem.with_suffix('.ms').write_text(text+',\nx1\n')
            reject('extra-prefix-restriction');stem.with_suffix('.ms').write_text(text)
    result=dict(status='PASS_TESTS_ONLY',test_count=len(checks),tests=checks,
        runtime_command_library_checks_mocked=True,terminal_records_explicitly_synthetic_and_removed=True,
        actual_branch_counts_verified=0,unrestricted_count=None,solver_processes_started=0,
        production_auditor_sha256=audit.digest((HERE/'exact_sign_branch_aggregate.py').read_bytes()))
    (HERE/'exact_sign_branch_terminal_check_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='tests'},indent=2))


if __name__=='__main__':main()
