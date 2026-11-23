#!/usr/bin/env python3
"""Independent finite-cap histogram and rotor bound audit; no full-board search."""
import hashlib
import json
from math import factorial, gcd
from pathlib import Path
import subprocess
import time

HERE=Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source=HERE/'exact_rotor_upper_review.cpp'
    executable=HERE/'exact_rotor_upper_review.bin'
    output=HERE/'exact_rotor_upper_review_results.json'
    if output.exists():
        raise FileExistsError(output)
    subprocess.run(['g++','-std=c++17','-O2','-Wall','-Wextra',str(source),'-o',str(executable)],check=True)
    start=time.monotonic()
    run=subprocess.run([str(executable)],text=True,capture_output=True,check=True,timeout=30)
    independent=json.loads(run.stdout)
    independent['wall_seconds']=time.monotonic()-start
    expected_path=HERE/'exact_rotor_upper_ternary4_census.json'
    expected=json.loads(expected_path.read_text())
    assert independent['assignments_examined']==3**15
    assert independent['caps']==expected['caps']
    assert independent['histogram']==expected['histogram']
    weighted=0
    for row in independent['histogram']:
        frequencies=[row[f'n{i}'] for i in range(4)]
        assert sum(frequencies)==27
        assert sum(i*n for i,n in enumerate(frequencies))==9
        # Given the cap, each encountered triple fixes a distinct initial
        # segment of its output permutation, leaving factorial(3-k) choices.
        weight=1
        for k,n in enumerate(frequencies):
            weight*=factorial(3-k)**n
        assert weight==6**row['n0']*2**row['n1']
        weighted+=row['caps']*weight
    old=3**19*6**27
    new=3**(19-7)*3*weighted
    assert weighted==743775294887298299068416
    assert new==1185818059470602086065654202368 and new<old
    d=gcd(new,old)
    result=dict(status='PASS_INDEPENDENT_BOUND_AUDIT', full_count=None,
                full_board_solver_started=False, independent_flat_enumeration=independent,
                fixed_boundary_cells=7, unrestricted_boundary_cells=19,
                remaining_boundary_cells=12, apex_restoration_factor=3,
                weighted_cap_sum_decimal=str(weighted), upper_bound_decimal=str(new),
                prior_upper_bound_decimal=str(old), exact_new_to_old_ratio=[new//d,old//d],
                proof_scope='injection of valid boards into rotor parameter tuples; cap condition is necessary only',
                source_sha256=digest(source),executable_sha256=digest(executable),
                owner_census_sha256=digest(expected_path),
                audit_source_sha256=digest(Path(__file__)))
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k]for k in ('status','upper_bound_decimal','exact_new_to_old_ratio')}))


if __name__=='__main__':main()
