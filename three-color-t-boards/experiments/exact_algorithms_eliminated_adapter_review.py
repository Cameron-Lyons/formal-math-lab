#!/usr/bin/env python3
"""Check all actual affine-eliminated backend exports and scope guards."""
from pathlib import Path
import hashlib,json,subprocess,sys
import exact_msolve_backend as backend
from exact_algorithms_branch_elimination_review import MANIFEST_SHA,parse

HERE=Path(__file__).resolve().parent
OUT=HERE/'exact_algorithms_eliminated_adapter_cases'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def check(meta,model,rep,k,prepared=False):
    n=96-k;label=rep['order']
    expected=dict(model='ternary-native-field-f3-affine-eliminated-branch',prime=3,field='F3',
        ring_type='ordinary polynomial ring',variables=n,coupled_variables=n-2,generators=n+81,
        count_divisor=1,count_multiplier=1,prefix='',fixed_prefix_rows=0,fixed_cell_count=0,
        fixed_original_cells=[],extension_variable=False,ternary_native_field=True,
        native_translation=True,native_e3=True,native_sign=False,native_sign_branch=k,
        native_branch_elimination=True,native_affine_elimination=True,
        native_variable_order='natural' if label=='natural' else 'minimum-fill',
        field_domain_equations=n,offset_variable_index=n-2,sign_variable_index=n-1,
        required_branch_ids=[0,1,2,3],branch_manifest_sha256=MANIFEST_SHA,
        input_sha256=rep['input_sha256'],branch_model_source_sha256=rep['metadata_sha256'],
        source_sha256=rep['input_sha256'] if prepared else rep['metadata_sha256'],
        status='PREPARED_NOT_RUN',standard_basis_complete=False)
    for key,value in expected.items():assert meta.get(key)==value,(key,meta.get(key),value)
    assert type(meta['native_sign_branch']) is int
    assert meta['count_scope']==f'full labeled boards in branch {k}'
    direct=['scope','full_count_rule','branch_original_condition','branch_canonical_condition',
            'original_color_reconstruction','canonical_color_affine_forms','inverse_reconstruction',
            'new_index_to_old97_index']
    for key in direct:assert meta[key]==model[key]
    for a,b in [('original_color_polynomials','original_color_degree_at_most2_polynomials'),
                ('old97_affine_reconstruction','all_old97_affine_polynomials_in_new_variables'),
                ('selected_old97_pivots','selected_pivots_in_old97_indices')]:assert meta[a]==model[b]
    assert not any(key in meta for key in ['original_color_linear_forms','canonical_color_linear_forms',
             'original_color_bilinear_polynomials','dimension_decimal','board_count_decimal'])
    if prepared:assert meta['basis_complete'] is False


def main():
    manifest_path=HERE/'exact_f3_branch_elimination_manifest.json'
    assert sha(manifest_path)==MANIFEST_SHA
    manifest=json.loads(manifest_path.read_text());OUT.mkdir(exist_ok=False)
    cases=[]
    for entry in manifest['branches']:
        k=entry['branch_id']
        for rep in entry['representations']:
            label=rep['order'];order=None if label=='natural' else 'minimum-fill'
            model=json.loads((HERE/rep['metadata']).read_text());text=(HERE/rep['input']).read_text()
            kwargs=dict(prime=3,ternary_native_field=True,native_translation=True,native_e3=True,
                        native_sign_branch=k,native_order=order,native_branch_elimination=True)
            actual,meta=backend.definitions(**kwargs)
            assert actual==text;check(meta,model,rep,k)
            assert parse(actual)[0]==96-k and len(parse(actual)[1])==177-k
            output=OUT/f'branch{k}_{label}'
            command=[sys.executable,str(HERE/'exact_msolve_backend.py'),'--prime','3',
                '--ternary-native-field','--native-e3','--native-translation',
                '--native-sign-branch',str(k),'--native-branch-elimination',
                '--prepare-only','--output',str(output)]
            if order:command+=['--native-order',order]
            p=subprocess.run(command,capture_output=True,text=True,timeout=20)
            output.with_suffix('.cli.log').write_text(p.stdout+p.stderr)
            assert p.returncode==0,p.stderr
            assert output.with_suffix('.ms').read_text()==text
            check(json.loads(output.with_suffix('.json').read_text()),model,rep,k,prepared=True)
            assert not output.with_suffix('.basis').exists()
            cases.append(dict(branch=k,order=label,input_sha256=sha(output.with_suffix('.ms')),
                              variables=96-k,generators=177-k))
    valid=dict(prime=3,ternary_native_field=True,native_translation=True,native_e3=True,
               native_sign_branch=0,native_branch_elimination=True)
    overrides=[{'native_sign_branch':None},{'native_sign_branch':False},{'native_sign_branch':True},
        {'native_sign_branch':0.0},{'native_sign_branch':'0'},{'native_sign_branch':-1},{'native_sign_branch':4},
        {'prime':2},{'prime':29},{'prefix':'0'},{'binary':True},{'fixture':'domain'},
        {'pivot_order':True},{'ternary_reduced':'all'},{'histogram_e2':True},
        {'ternary_prefix_sums':'all'},{'prefix_field_equations':True},{'histogram_e4':True},
        {'ternary_native_field':False},{'native_translation':False},{'native_e3':False},
        {'native_sign':True},{'native_order':'natural'}]
    for override in overrides:
        try:backend.definitions(**(valid|override))
        except ValueError:pass
        else:raise AssertionError(('invalid scope accepted',override))
    for kwargs in [dict(native_branch_elimination=True),dict(native_branch_elimination=True,native_sign_branch=0)]:
        try:backend.definitions(**kwargs)
        except ValueError:pass
        else:raise AssertionError('elimination option ignored')
    bad_flags=[['--native-branch-elimination'],['--native-branch-elimination','--native-sign-branch','0'],
        ['--prime','3','--ternary-native-field','--native-translation','--native-sign-branch','0','--native-branch-elimination'],
        ['--prime','3','--ternary-native-field','--native-e3','--native-translation','--native-sign',
         '--native-sign-branch','0','--native-branch-elimination']]
    for i,flags in enumerate(bad_flags):
        output=OUT/f'reject{i}'
        p=subprocess.run([sys.executable,str(HERE/'exact_msolve_backend.py'),*flags,
            '--prepare-only','--output',str(output)],capture_output=True,text=True,timeout=20)
        output.with_suffix('.cli.log').write_text(p.stdout+p.stderr)
        assert p.returncode!=0 and not output.with_suffix('.ms').exists()
    result=dict(status='PASS',scope='actual affine-eliminated adapter definitions and CLI preparation; no solver',
        actual_prepared_variants=cases,definition_rejections=len(overrides)+2,cli_rejections=len(bad_flags),
        branch_zero_explicit=True,affine_constants_preserved=True,old_aggregator_discriminator_present=True,
        source_model_review='exact_algorithms_branch_elimination_review.json',solver_runs=0,
        backend_sha256=sha(HERE/'exact_msolve_backend.py'),
        helper_sha256=sha(HERE/'exact_msolve_native_branch_elimination.py'),reviewer_sha256=sha(Path(__file__)))
    (HERE/'exact_algorithms_eliminated_adapter_review.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
