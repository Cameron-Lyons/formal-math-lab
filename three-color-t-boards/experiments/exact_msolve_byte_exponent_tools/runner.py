#!/usr/bin/env python3
"""Compare completed bases against the preserved export-only msolve build."""
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
EXPERIMENTS = ROOT.parent
sys.path.insert(0, str(EXPERIMENTS))
from exact_msolve_backend import definitions, parse_leading
from exact_algebra_backend import monomial_dimension
from exact_standard_monomials import count_standard_monomials, MissingPurePowerBounds

SIX_PREFIX = '100011101011000101010011112112211212021201221022121202020220010222002102100022222'


def execute(name, kind, text, mode, seconds=20, la=2):
    executable = (ROOT if kind == 'selective' else
                  EXPERIMENTS / 'exact_msolve_symbolic_reserve_tools') / 'msolve'
    stem = ROOT / (name + '_' + kind + '_g' + str(mode))
    source, basis = stem.with_suffix('.ms'), stem.with_suffix('.basis')
    if source.exists() or basis.exists():
        raise ValueError('refusing to replace a prior test: ' + str(stem))
    source.write_text(text)
    command = [str(executable), '-f', str(source), '-o', str(basis),
               '-g', str(mode), '-s', '4', '-l', str(la), '-t', '1', '-r', '1', '-c', '0', '-v', '2']
    env = dict(os.environ)
    env['LD_LIBRARY_PATH'] = str(EXPERIMENTS / 'exact_algebra_backend_root/usr/lib')

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (2048 * 1024**2,) * 2)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    timed_out = False
    try:
        process = subprocess.run(command, text=True, capture_output=True, env=env,
                                 preexec_fn=limits, timeout=seconds)
        log, code = process.stdout + process.stderr, process.returncode
    except subprocess.TimeoutExpired as error:
        timed_out, code = True, None
        log = (error.stdout or b'').decode() if isinstance(error.stdout, bytes) else (error.stdout or '')
        log += (error.stderr or b'').decode() if isinstance(error.stderr, bytes) else (error.stderr or '')
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    stem.with_suffix('.log').write_text(log)
    data = basis.read_text() if basis.exists() else ''
    events = [dict(zip(('nonpivot', 'referenced', 'inserted', 'basis_capacity'), map(int, m)))
              for m in re.findall(r'MSOLVE_PROMOTION_COLUMNS nonpivot=(\d+) referenced=(\d+) '
                                  r'inserted=(\d+) basis_capacity=(\d+)', log)]
    capacity_requests = [dict(zip(('required_with_spare', 'exponent_old', 'exponent_new', 'buckets_old', 'buckets_new'), map(int, m)))
                         for m in re.findall(r'MSOLVE_PROMOTION_CAPACITY_REQUEST required_with_spare=(\d+) exponent_old=(\d+) exponent_new=(\d+) buckets_old=(\d+) buckets_new=(\d+)', log)]
    reservations = [dict(zip(('nonpivot', 'referenced', 'missing', 'basis_load', 'basis_capacity'), map(int, m)))
                    for m in re.findall(r'MSOLVE_PROMOTION_RESERVATION nonpivot=(\d+) referenced=(\d+) '
                                        r'missing=(\d+) basis_load=(\d+) basis_capacity=(\d+)', log)]
    if kind == 'selective':
        assert len(reservations) == len(events)
        assert all(a['missing'] == b['inserted'] and a['referenced'] == b['referenced']
                   for a, b in zip(reservations, events))
    staging_events = [dict(zip(('old_load','old_capacity','missing','old_exponent_bytes','staged_exponent_bytes','reset_capacity'),map(int,m))) for m in re.findall(r'MSOLVE_SYMBOLIC_STAGING old_load=(\d+) old_capacity=(\d+) missing=(\d+) old_exponent_bytes=(\d+) staged_exponent_bytes=(\d+) reset_capacity=(\d+)',log)]
    symbolic_requests = [dict(zip(('old_load','row_length','required_with_spare','requested_capacity'),map(int,m))) for m in re.findall(r'MSOLVE_SYMBOLIC_ROW_RESERVE old_load=(\d+) row_length=(\d+) required_with_spare=(\d+) requested_capacity=(\d+)',log)]
    for event in symbolic_requests:
        assert event['required_with_spare']==event['old_load']+event['row_length']+1
        assert event['requested_capacity']>=event['required_with_spare']
    record = dict(symbolic_requests=symbolic_requests,staging_events=staging_events,name=name, kind=kind, mode=mode, command=command, returncode=code,
                  timed_out=timed_out, memory_mb=2048, timeout_seconds=seconds,
                  wall_seconds=time.monotonic()-start,
                  cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
                  marker_count=sum(line.strip() == 'MSOLVE_PRIME_GB_EXPORT_COMPLETE' for line in log.splitlines()),
                  error_diagnostics=[line for line in log.splitlines()
                                     if re.search(r'\berror\b|out of memory|cannot allocate|segmentation|aborted', line, re.I)],
                  basis_sha256=hashlib.sha256(data.encode()).hexdigest(),
                  input_sha256=hashlib.sha256(text.encode()).hexdigest(),
                  executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest(),
                  basis_file=str(basis), promotion_events=events, reservation_events=reservations, capacity_requests=capacity_requests)
    stem.with_suffix('.json').write_text(json.dumps(record, indent=2) + '\n')
    assert code == 0 and not timed_out and record['marker_count'] == 1 and not record['error_diagnostics'], record
    return record, data


def main():
    fixtures = [
        ('f3_domain', 1, ['x1^3-1'], 3),
        ('f3_domain_pair', 2, ['x1^3-1', 'x2^3-1'], 9),
        ('f3_root_sum', 3, ['x1^3-1', 'x2^3-1', 'x3^3-1', 'x1+x2+x3'], 9),
        ('f3_mixed', 2, ['x1^3-1', 'x2^3-1', 'x1*x2-1'], 3),
        ('f3_mixed_chain', 4, [f'x{i}^3-1' for i in range(1, 5)] + ['x1*x2-x3', 'x2*x3-x4'], 9),
        ('f3_unit', 1, ['x1^3-1', '1'], 0),
        ('f3_positive_dimension', 2, ['x1'], None),
    ]
    cases=[]
    for name,n,eq,expected in fixtures:
        text=','.join(f'x{i+1}' for i in range(n))+'\n3\n'+',\n'.join(eq)+'\n'
        cases.append((name,text,n,3,expected))
    natural=(EXPERIMENTS/'exact_native_field_probe_runs/ternary_six.ms').read_text()
    assert len(natural.splitlines()[0].split(','))==19 and natural.splitlines()[1]=='3'
    cases.append(('natural_f3_six',natural,19,3,6))
    for prime in [2,5]:
        text='x1,x2\n'+str(prime)+'\nx1^3-1,\nx2^3-1,\nx1*x2-1\n'
        cases.append((f'unchanged_f{prime}',text,2,prime,3))
    cases.append(('f2_mixed_chain', 'x1,x2,x3,x4\n2\nx1^3+1,x2^3+1,x3^3+1,x4^3+1,x1*x2+x3,x2*x3+x4\n',4,2,9))
    cases.append(('f2_cover', 'x1,x2,x3\n2\nx1^3+1,x2^3+1,x3^3+1,x1+x2+x3\n',3,2,6))
    results=[]
    for name,text,n,prime,expected in cases:
        for mode in [1,2]:
            old,a=execute(name,'baseline',text,mode,seconds=30)
            new,b=execute(name,'selective',text,mode,seconds=30)
            assert a==b,(name,mode)
            if prime!=2:
                assert 'MSOLVE_F2_BITSET ' not in Path(new['basis_file']).with_suffix('.log').read_text()
            if prime==5:assert not new['staging_events']
            counts=[]
            if mode==1:
                for basis in [a,b]:
                    leading=parse_leading(basis,n,prime)
                    if expected is None:
                        try:count_standard_monomials(leading,n,standard_basis_complete=True)
                        except MissingPurePowerBounds:pass
                        else:raise AssertionError('nonfinite ideal accepted')
                    else:
                        q=monomial_dimension(leading,n)[0]
                        r=count_standard_monomials(leading,n,standard_basis_complete=True)
                        assert q==r==expected,(name,q,r,expected)
                        counts.append(dict(quotient_dimension=str(q),independent_dimension=str(r)))
            results.append(dict(fixture=name,prime=prime,variables=n,mode=mode,status='COMPLETE',
                                expected_quotient_dimension=None if expected is None else str(expected),
                                exports_byte_identical=True,counts=counts,runs=[old,new]))
            print(name,mode,'PASS','staging events',len(new['staging_events']),flush=True)
    f3events=[event for result in results if result['prime']==3 for run in result['runs'] if run['kind']=='selective' for event in run['staging_events']]
    assert f3events,'F3 staging never exercised'
    symbolic_events=[event for result in results for run in result['runs'] if run['kind']=='selective' for event in run['symbolic_requests']]
    assert symbolic_events, 'symbolic reserve never exercised'
    report=dict(symbolic_reserve_events=symbolic_events,status='PASS',complete_basis_comparisons=len(results),f3_staging_events=f3events,
                full_board_solver_runs=0,results=results)
    (ROOT/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS',len(results),'completed comparisons;',len(f3events),'F3 staging events')

if __name__=='__main__':main()
