#!/usr/bin/env python3
"""Read/recount the completed transformed nine-row fiber; never rerun solver."""
from itertools import product
from pathlib import Path
import hashlib
import json
import re

import exact_msolve_backend as backend
import exact_msolve_prefix_sums as exporter
from exact_algebra_backend import monomial_dimension
from exact_standard_monomials import count_standard_monomials
from exact_pivot_review_common import geometry,solve_linears,input_polynomials

HERE=Path(__file__).resolve().parent
STEM=HERE/'exact_msolve_elementary_analysis_six_fiber'


def main():
    model=json.loads(exporter.SOURCE.read_text())
    source_hash=hashlib.sha256(exporter.SOURCE.read_bytes()).hexdigest()
    assert source_hash=='7f8251ab52e8d6869c19cc861dc98b0c1e66904313b0d87920d9f95659700092'
    # Recheck all eight current exporter/backend definitions against the prior
    # independently verified inputs after the metadata-only provenance fix.
    refreshed=[]
    for all_moments,e2,field in product((False,True),repeat=3):
        mode='all' if all_moments else 'representatives'
        name=f'{mode}_e{int(e2)}_f{int(field)}'
        text,meta=backend.definitions(prime=2,ternary_prefix_sums=mode,
                                    histogram_e2=e2,prefix_field_equations=field)
        assert text==(HERE/'exact_pivot_review_prefix_prepared'/name).with_suffix('.ms').read_text()
        assert meta['prefix_model_source_sha256']==source_hash
        assert meta['prefix_exporter_sha256']==hashlib.sha256(Path(exporter.__file__).read_bytes()).hexdigest()
        refreshed.append(dict(mode=name,input_sha256=hashlib.sha256(text.encode()).hexdigest()))
    result=json.loads(STEM.with_suffix('.json').read_text())
    assert result['status']=='COMPLETE' and type(result['returncode']) is int and result['returncode']==0
    assert result['basis_complete'] is True and result['standard_basis_complete'] is True
    assert result['export_marker_count']==1 and result['error_diagnostics']==[]
    assert result['variables']==97 and result['generators']==358 and result['count_divisor']==2
    assert result['count_multiplier']==1 and result['symmetry_normalization'] is False
    assert result['prefix_model_source_sha256']==source_hash
    prefix=result['prefix'];assert len(prefix)==81 and set(prefix)<=set('012')
    assert result['fixed_original_cells']==list(range(81)) and len(result['equation_labels'])==358
    _,roles=geometry();order=model['original_cell_order']
    unary=[]
    for cells in roles.values():
        row=set()
        for j,cell in enumerate(order):
            if cell in cells:
                row ^= {j}
                if j:row ^= {j-1}
        unary.append(row)
    substitutions=solve_linears(unary,model['eliminated_prefix_variables'])
    free=model['free_prefix_variables'];index={v:i for i,v in enumerate(free)}
    yforms=[substitutions.get(i,{i}) for i in range(100)]
    zforms={cell:yforms[i]^(yforms[i-1] if i else set()) for i,cell in enumerate(order)}
    base,metadata=exporter.prefix_definitions(True,True,True)
    assert result['base_input_sha256']==hashlib.sha256(base.encode()).hexdigest()
    expected=input_polynomials(base,96)
    for cell,color in enumerate(prefix):
        polynomial={(index[v],) for v in zforms[cell]}
        polynomial ^= ({()} if color=='0' else {(96,)} if color=='1' else {(96,),()})
        expected.append(polynomial)
    expected.append({(96,96),(96,),()})
    raw_input=STEM.with_suffix('.ms').read_text()
    assert raw_input.splitlines()[0]==','.join([f'x{i+1}' for i in range(96)]+['a'])
    assert input_polynomials(re.sub(r'\ba\b','x97',raw_input),97)==expected
    assert hashlib.sha256(raw_input.encode()).hexdigest()==result['input_sha256']
    log=STEM.with_suffix('.log').read_text()
    assert log.splitlines().count('MSOLVE_PRIME_GB_EXPORT_COMPLETE')==1
    assert not re.search(r'error|segmentation|allocation failed|out of memory|cannot allocate',log,re.I)
    basis=STEM.with_suffix('.basis').read_text()
    headers=re.findall(r'^#variable order:\s*(.*?)\s*$',basis,re.M)
    assert len(headers)==1 and [x.strip() for x in headers[0].split(',')]==[f'x{i+1}' for i in range(96)]+['a']
    leading=backend.parse_leading(re.sub(r'\ba\b','x97',basis),97,2)
    exported=json.loads(STEM.with_suffix('.leading.json').read_text())
    assert exported['format']=='leading-monomial-ideal-v1' and exported['variables']==97
    assert exported['standard_basis_complete'] is True and exported['leading_monomials']==leading
    assert exported['provenance']['input_sha256']==result['input_sha256']
    assert exported['provenance']['basis_sha256']==hashlib.sha256(basis.encode()).hexdigest()==result['basis_sha256']
    assert exported['provenance']['executable_sha256']==result['executable_sha256']
    assert hashlib.sha256(Path(result['command'][0]).read_bytes()).hexdigest()==result['executable_sha256']
    one=monomial_dimension(leading,97)[0]
    two=count_standard_monomials(leading,97,standard_basis_complete=True)
    assert one==two==12 and int(result['quotient_dimension'])==int(result['independent_count'])==12
    assert result['board_count']=='6' and one//result['count_divisor']==6
    outer=json.loads(STEM.with_suffix('.outer.json').read_text())
    assert outer['status']=='POSTPROCESS_RECOVERED_COMPLETE' and outer['solver_runs']==1
    assert outer['no_solver_rerun'] is True
    assert 'variable order mismatch' in STEM.with_suffix('.outer.log').read_text()
    assert result['child_cpu_seconds'] is None and result['child_wall_seconds'] is None
    report=dict(status='PASS',solver_processes_started=0,actual_input_polynomials_checked=358,
        variables=97,leading_monomials=len(leading),quotient_dimension_decimal='12',
        count_divisor=2,board_count_decimal='6',count_scope='one fixed nine-row fiber only',
        both_independent_counters_agree=True,input_sha256=result['input_sha256'],
        actual_header_checked_before_identifier_alias=True,metadata_corrections=result.get('metadata_corrections'),
        original_outer_parser_failure_preserved=True,no_solver_rerun=True,
        timing_semantics='Only rounded solver-reported3.14CPU/3.17wall retained; exact subprocessCPU/wall unavailable.',
        current_exporter_sha256=hashlib.sha256(Path(exporter.__file__).read_bytes()).hexdigest(),
        current_exporter_eight_inputs_unchanged=refreshed,
        source_model_sha256=source_hash,full_count_status='NOT_COMPUTED',
        artifact_sha256={suffix:hashlib.sha256(STEM.with_suffix(suffix).read_bytes()).hexdigest()
                         for suffix in ('.json','.ms','.basis','.leading.json','.log','.outer.json','.outer.log')})
    (HERE/'exact_pivot_review_six_fiber_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('artifact_sha256','current_exporter_eight_inputs_unchanged','metadata_corrections')},indent=2))


if __name__=='__main__':main()
