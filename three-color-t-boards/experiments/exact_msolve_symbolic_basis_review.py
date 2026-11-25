#!/usr/bin/env python3
"""Independent completed F2/F3 bases for the checked symbolic-row reserve."""
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess

from exact_msolve_sparse_review import buchberger,leading,parse_full_basis,parse_polynomial,reduce_polynomial
from exact_standard_monomials import count_standard_monomials

HERE=Path(__file__).resolve().parent
TREE='msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2'


def main():
    baseline_root=HERE/'exact_msolve_staged_f3_tools'
    candidate_root=HERE/'exact_msolve_symbolic_reserve_tools'
    old=baseline_root/TREE/'src';new=candidate_root/TREE/'src'
    old_files={p.relative_to(old) for p in old.rglob('*.c')}
    new_files={p.relative_to(new) for p in new.rglob('*.c')}
    assert old_files==new_files
    changed=[p for p in sorted(old_files) if (old/p).read_bytes()!=(new/p).read_bytes()]
    assert changed==[Path('neogb/hash.c'),Path('neogb/symbol.c')]
    symbol=(new/'neogb/symbol.c').read_text()
    assert symbol.count('reserve_symbolic_row_capacity(sht, b, md);')==3
    stripped=re.sub(r'^\s*reserve_symbolic_row_capacity\(sht, b, md\);\n','',symbol,flags=re.M)
    assert stripped==(old/'neogb/symbol.c').read_text()
    baseline,candidate=baseline_root/'msolve',candidate_root/'msolve'
    output=HERE/'exact_msolve_symbolic_basis_review_runs';output.mkdir(exist_ok=False)
    source_paths=sorted((HERE/'exact_msolve_staged_basis_review_runs').glob('*.ms'))
    source_paths+=sorted((HERE/'exact_msolve_staged_f3_review_runs').glob('*.ms'))
    assert len(source_paths)==24
    env=dict(os.environ,LD_LIBRARY_PATH=str(HERE/'exact_algebra_backend_root/usr/lib'))
    def limits():
        resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,)*2)
        resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    reports=[]
    for source in source_paths:
        text=source.read_text();lines=text.splitlines()
        variables=len(lines[0].split(','));prime=int(lines[1]);assert prime in (2,3)
        equations=''.join(lines[2:]).split(',')
        original=[parse_polynomial(e,variables,prime) for e in equations]
        expected=buchberger(original,prime)
        assert all(not reduce_polynomial(p,expected,prime) for p in original)
        dimension=count_standard_monomials([leading(p) for p in expected],variables,standard_basis_complete=True)
        name=f'p{prime}_{source.stem}';input_path=output/(name+'.ms');input_path.write_text(text)
        runs=[]
        for label,executable in [('baseline',baseline),('candidate',candidate)]:
            basis_path=output/(name+'_'+label+'.basis')
            command=[str(executable),'-g','2','-l','2','-t','1','-r','1','-c','0',
                     '-v','2','-m','16','-s','4','-f',str(input_path),'-o',str(basis_path)]
            result=subprocess.run(command,capture_output=True,text=True,timeout=10,env=env,preexec_fn=limits)
            log=result.stdout+result.stderr;(output/(name+'_'+label+'.log')).write_text(log)
            assert result.returncode==0,(name,label,log[-2000:])
            assert log.splitlines().count('MSOLVE_PRIME_GB_EXPORT_COMPLETE')==1
            assert not re.search(r'\berror\b|out of memory|cannot allocate|segmentation',log,re.I)
            assert parse_full_basis(basis_path.read_text(),variables,prime)==expected
            if prime==3:assert 'MSOLVE_F2_BITSET rows=' not in log
            runs.append(dict(label=label,command=command,
                basis_sha256=hashlib.sha256(basis_path.read_bytes()).hexdigest(),
                symbolic_reserve_rounds=log.count('MSOLVE_SYMBOLIC_ROW_RESERVE '),
                staging_rounds=log.count('MSOLVE_SYMBOLIC_STAGING '),returncode=result.returncode))
        assert runs[0]['basis_sha256']==runs[1]['basis_sha256']
        assert runs[0]['symbolic_reserve_rounds']==0
        reports.append(dict(name=name,prime=prime,variables=variables,generators=len(equations),
            fixture_source=str(source),input_sha256=hashlib.sha256(text.encode()).hexdigest(),
            quotient_dimension_decimal=str(dimension),complete_basis_matches_python=True,
            byte_identical_to_prior_build=True,runs=runs))
    result=dict(status='PASS',fixtures=24,full_basis_comparisons=48,
        changed_C_files=list(map(str,changed)),unchanged_C_files=len(old_files)-len(changed),
        ordinary_constructor_callsite_changes=3,
        candidate_sha256=hashlib.sha256(candidate.read_bytes()).hexdigest(),
        baseline_sha256=hashlib.sha256(baseline.read_bytes()).hexdigest(),
        patch_sha256=hashlib.sha256((candidate_root/'symbolic-row-reserve.patch').read_bytes()).hexdigest(),
        symbolic_reserve_rounds_by_prime={str(p):sum(r['runs'][1]['symbolic_reserve_rounds'] for r in reports if r['prime']==p) for p in (2,3)},
        staging_rounds_by_prime={str(p):sum(r['runs'][1]['staging_rounds'] for r in reports if r['prime']==p) for p in (2,3)},
        full_board_solver_runs=0,memory_limit_bytes=2*1024**3,results=reports)
    assert all(result['symbolic_reserve_rounds_by_prime'].values())
    (HERE/'exact_msolve_symbolic_basis_review_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))


if __name__=='__main__':main()
