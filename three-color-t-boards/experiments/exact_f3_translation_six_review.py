#!/usr/bin/env python3
"""Read/recount the completed translated nine-row fiber; no solver rerun."""
from pathlib import Path
import hashlib
import json
import re

from exact_f3_review import add,parse_input
from exact_msolve_backend import parse_leading
from exact_standard_monomials import count_standard_monomials
from exact_algebra_backend import monomial_dimension

HERE=Path(__file__).resolve().parent


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def rank(rows):
    rows=[list(row) for row in rows];rank=0
    for col in range(len(rows[0])):
        found=next((j for j in range(rank,len(rows)) if rows[j][col]),None)
        if found is None:continue
        rows[rank],rows[found]=rows[found],rows[rank]
        inv=pow(rows[rank][col],-1,3);rows[rank]=[inv*c%3 for c in rows[rank]]
        for j in range(len(rows)):
            if j!=rank:
                c=rows[j][col];rows[j]=[(a-c*b)%3 for a,b in zip(rows[j],rows[rank])]
        rank+=1
        if rank==len(rows):break
    return rank


def main():
    stem=HERE/'exact_f3_translation_six'
    result=json.loads(stem.with_suffix('.json').read_text())
    outer=json.loads(stem.with_suffix('.outer.json').read_text())
    model=json.loads((HERE/'exact_f3_translation_model.json').read_text())
    fixes=json.loads(stem.with_suffix('.fixes.json').read_text())
    base=(HERE/'exact_f3_translation_e3.ms').read_text()
    source=stem.with_suffix('.ms').read_text()
    assert source.startswith(base.rstrip('\n')+',\n')
    actual=parse_input(source);base_polynomials=parse_input(base)
    assert actual[:176]==base_polynomials and len(actual)==257
    prefix=result['prefix'];assert len(prefix)==81 and prefix[0]=='1'
    assert len(fixes)==81
    rows=[]
    for cell,color in enumerate(map(int,prefix)):
        form={int(i):c for i,c in model['original_color_linear_forms'][str(cell)].items()}
        wanted=add({(i,):c for i,c in form.items()},{():color},-1)
        assert actual[176+cell]==wanted
        assert fixes[cell]['original_cell']==cell and fixes[cell]['color']==color
        assert {int(i):c for i,c in fixes[cell]['linear_form'].items()}==form
        row=[form.get(i,0) for i in range(96)]+[color]
        rows.append(row)
    assert actual[176]=={(95,):1,():2}
    assert rank([row[:-1] for row in rows])==rank(rows)==80
    assert result['prefix_fix_coefficient_rank']==result['prefix_fix_augmented_rank']==80
    assert result['status']=='COMPLETE_VERIFIED' and result['basis_complete'] is True
    assert result['returncode']==0 and outer['returncode']==0 and outer['status']=='COMPLETE'
    assert result['count_divisor']==result['count_multiplier']==1 and not result['extension_variable']
    assert result['variables']==96 and result['generators']==257
    assert result['fixed_original_cell_count']==81 and result['offset_fixed_to']==1
    assert result['input_sha256']==sha(stem.with_suffix('.ms'))
    assert result['base_input_sha256']==hashlib.sha256(base.encode()).hexdigest()
    assert result['model_sha256']==sha(HERE/'exact_f3_translation_model.json')
    assert result['executable_sha256']==sha(Path(result['command'][0]))
    assert result['executable_sha256']=='9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a'
    log=stem.with_suffix('.log').read_text()
    assert log.splitlines().count('MSOLVE_PRIME_GB_EXPORT_COMPLETE')==result['export_marker_count']==1
    assert not re.search(r'\berror\b|out of memory|cannot allocate|segmentation|aborted',log,re.I)
    assert not result['error_diagnostics'] and sha(stem.with_suffix('.log'))==result['log_sha256']
    assert sha(stem.with_suffix('.basis'))==result['basis_sha256']
    leading=parse_leading(stem.with_suffix('.basis').read_text(),96,3)
    exported=json.loads(stem.with_suffix('.leading.json').read_text())
    assert exported['standard_basis_complete'] is True and exported['variables']==96
    assert exported['leading_monomials']==leading and len(leading)==result['basis_size']==101
    for key in ('input_sha256','executable_sha256','basis_sha256'):
        assert exported['provenance'][key]==result[key]
    a=count_standard_monomials(leading,96,standard_basis_complete=True)
    b,_=monomial_dimension(leading,96,seconds=10)
    assert a==b==6==int(result['dimension_decimal'])==int(result['independent_dimension_decimal'])==int(result['board_count_decimal'])
    report=dict(status='PASS',scope='fixed nine-row fiber, not the unrestricted count',
        input_sha256=result['input_sha256'],basis_sha256=result['basis_sha256'],
        complete_input_polynomials_compared=257,fixed_original_cells=list(range(81)),
        actual_apex_equation='2+x96',prefix_fix_rank=80,variables=96,leading_monomials=101,
        completed_export_marker_count=1,solver_exit_code=0,
        independently_recounted_quotient_dimension_decimal='6',board_count_decimal='6',
        count_divisor=1,count_multiplier=1,free_offset_factor_remains=False,
        child_cpu_seconds=result['child_cpu_seconds'],child_wall_seconds=result['child_wall_seconds'],
        solver_runs_by_this_review=0)
    (HERE/'exact_f3_translation_six_review_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='fixed_original_cells'},indent=2))


if __name__=='__main__':main()
