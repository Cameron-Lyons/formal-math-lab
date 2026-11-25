#!/usr/bin/env python3
"""Tiny exhaustive F4 coordinate fixtures, then exact completed basis counts."""
from itertools import product
from pathlib import Path
import hashlib
import json
import os
import resource
import subprocess
import time

from exact_msolve_elementary_analysis import MUL, serialize
from exact_msolve_backend import parse_leading
from exact_algebra_backend import monomial_dimension
from exact_standard_monomials import count_standard_monomials

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'exact_msolve_elementary_analysis_fixtures'
EXE=ROOT/'exact_msolve_f2_bitset_tools/msolve'


def domain(i):
    a=1 << (4*i)
    if i==0:return {3*a,0}
    b=1 << (4*(i-1))
    return {3*a,2*a+b,a+2*b,3*b,0}


def limits():
    resource.setrlimit(resource.RLIMIT_AS,(2048*1024**2,)*2)
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))


def main():
    OUT.mkdir(exist_ok=False)
    results=[]
    for name,n,extra,field_equations,expected in (
            ('two_independent_colors',2,[],False,9),
            ('two_colors_with_field_equations',2,[],True,9),
            ('zero_prefix_coordinate_allowed',2,[('zero_y1',{1 << 4})],False,3),
            ('fixed_valid',2,[('one_y0',{1,0}),('zero_y1',{1 << 4})],False,1),
            ('fixed_invalid_zero_color',2,[('zero_y0',{1})],False,0),
            ('three_independent_colors',3,[],False,27),
            ('three_distinct_colors',3,[('sum_zero',{1 << 8})],False,6),
            ('three_distinct_normalized',3,[('sum_zero',{1 << 8}),('one_y0',{1,0})],False,2)):
        polys=[(f'domain:{i}',domain(i)) for i in range(n)]+extra
        if field_equations:polys += [(f'field:{i}',{1 << (4*i),4 << (4*i)}) for i in range(n)]
        direct=0
        for y in product(range(4),repeat=n):
            z=[y[i] ^ (y[i-1] if i else 0) for i in range(n)]
            allowed=all(z)
            if name=='zero_prefix_coordinate_allowed':allowed &= y[1]==0
            if name=='fixed_valid':allowed &= y[0]==1 and y[1]==0
            if name=='fixed_invalid_zero_color':allowed &= y[0]==0
            if name.startswith('three_distinct'):allowed &= y[2]==0
            if name=='three_distinct_normalized':allowed &= y[0]==1
            direct += int(allowed)
        assert direct==expected
        text=serialize(polys,n);source=OUT/(name+'.ms');basis=OUT/(name+'.basis');source.write_text(text)
        command=[str(EXE),'-f',str(source),'-o',str(basis),'-g','1','-l','2','-t','1','-r','1','-c','0','-v','2']
        env=dict(os.environ,LD_LIBRARY_PATH=str(ROOT/'exact_algebra_backend_root/usr/lib'))
        before=resource.getrusage(resource.RUSAGE_CHILDREN);start=time.monotonic()
        p=subprocess.run(command,capture_output=True,text=True,env=env,preexec_fn=limits,timeout=15)
        after=resource.getrusage(resource.RUSAGE_CHILDREN);log=p.stdout+p.stderr
        (OUT/(name+'.log')).write_text(log)
        assert p.returncode==0 and log.splitlines().count('MSOLVE_PRIME_GB_EXPORT_COMPLETE')==1
        leads=parse_leading(basis.read_text(),n,2)
        first=monomial_dimension(leads,n)[0]
        second=count_standard_monomials(leads,n,standard_basis_complete=True)
        assert first==second==direct==expected
        results.append(dict(name=name,variables=n,status='COMPLETE',quotient_dimension=str(first),
                            exhaustive_F4_assignments=4**n,exhaustive_F4_count=direct,
                            independent_count=str(second),command=command,returncode=p.returncode,
                            cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
                            wall_seconds=time.monotonic()-start,memory_mb=2048,timeout_seconds=15,
                            input_sha256=hashlib.sha256(text.encode()).hexdigest(),
                            basis_sha256=hashlib.sha256(basis.read_bytes()).hexdigest()))
    report=dict(status='PASS',fixtures=results,full_board_solver_runs=0,
                executable_sha256=hashlib.sha256(EXE.read_bytes()).hexdigest())
    (ROOT/'exact_msolve_elementary_analysis_fixture_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS',len(results),'tiny coordinate fixtures')


if __name__=='__main__':main()
