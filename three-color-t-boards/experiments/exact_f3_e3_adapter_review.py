#!/usr/bin/env python3
"""Check actual natural-F3/e3 backend output without starting a solver."""
from pathlib import Path
from unittest.mock import patch
import hashlib
import json

import exact_msolve_backend as backend
from exact_msolve_native_e3 import augment
from exact_f3_review import decode,parse_input

HERE=Path(__file__).resolve().parent


def main():
    base,metadata=backend.definitions(prime=3,ternary_native_field=True)
    text,augmented=backend.definitions(prime=3,ternary_native_field=True,native_e3=True)
    data=json.loads((HERE/'exact_f3_math_e3_constraints.json').read_text())
    expected=list(decode(data['equations']).values())
    assert parse_input(text)==parse_input(base)+expected
    assert text.startswith(base.rstrip('\n')+',\n')
    assert augmented['generators']==176 and augmented['field_domain_equations']==96
    assert augmented['retained_moment_equations']==76 and augmented['native_e3_generators']==4
    assert augmented['count_divisor']==augmented['count_multiplier']==1
    assert augmented['field']=='F3' and not augmented['extension_variable']
    assert augmented['prefix']=='' and augmented['fixed_original_cells']==[]
    assert augmented['symmetry_normalization'] is False
    assert augmented['free_prefix_variables']==metadata['free_prefix_variables']
    assert augmented['original_color_linear_forms']==metadata['original_color_linear_forms']
    assert augmented['pre_e3_input_sha256']==hashlib.sha256(base.encode()).hexdigest()
    digest=hashlib.sha256(text.encode()).hexdigest()
    assert digest=='cb2497554585e51166b747cee0221efc3cf7f130f46b9084d7f2e9d3b760c105'
    directory=HERE/'exact_f3_e3_review_prepared';directory.mkdir(exist_ok=False)
    with patch.object(backend.subprocess,'run',side_effect=AssertionError('solver forbidden')):
        prepared=backend.run(directory/'native_e3',prime=3,ternary_native_field=True,
            native_e3=True,prepare_only=True,require_export_marker=True,
            executable=HERE/'exact_msolve_staged_promotion_tools/msolve')
    assert (directory/'native_e3.ms').read_text()==text
    assert prepared['status']=='PREPARED_NOT_RUN' and prepared['basis_complete'] is False
    assert prepared['source_sha256']==digest==prepared['input_sha256']
    assert prepared['native_field_source_sha256']==data['native_source_sha256']
    assert prepared['native_e3_source_sha256']==hashlib.sha256((HERE/'exact_f3_math_e3_constraints.json').read_bytes()).hexdigest()
    assert 'dimension_decimal' not in prepared and 'board_count_decimal' not in prepared
    invalid_options=[dict(prime=2),dict(prime=29),dict(prefix='0'),dict(binary=True),
        dict(fixture='domain'),dict(pivot_order=True),dict(ternary_reduced='all'),
        dict(ternary_prefix_sums='all'),dict(histogram_e2=True),
        dict(prefix_field_equations=True),dict(histogram_e4=True),dict(ternary_native_field=False)]
    for change in invalid_options:
        options=dict(prime=3,ternary_native_field=True,native_e3=True);options.update(change)
        try:backend.definitions(**options)
        except ValueError:pass
        else:raise AssertionError(('conflicting scope accepted',change))
    for key,value in [('prime',2),('variables',100),('count_divisor',2),('prefix','0'),
                      ('retained_unary_quadratic_moments',0),('native_field_source_sha256','bad')]:
        altered=dict(metadata);altered[key]=value
        try:augment(base,altered)
        except ValueError:pass
        else:raise AssertionError(('invalid base accepted',key))
    result=dict(status='PASS',input_sha256=digest,pre_e3_input_sha256=augmented['pre_e3_input_sha256'],
        source_sha256=prepared['native_e3_source_sha256'],base_verbatim=True,
        independently_compared_added_polynomials=4,added_terms=574,variables=96,generators=176,
        domain_equations=96,retained_moments=76,count_divisor=1,count_multiplier=1,
        invalid_option_combinations=len(invalid_options),invalid_base_metadata_cases=6,
        prepared_input=str(directory/'native_e3.ms'),prepare_status=prepared['status'],
        adapter_sha256=hashlib.sha256(Path(backend.__file__).read_bytes()).hexdigest(),solver_runs=0)
    (HERE/'exact_f3_e3_adapter_review_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
