#!/usr/bin/env python3
"""Independent audits of fresh original-cell pivot exports; no solver."""
from pathlib import Path
import hashlib
import json

from exact_pivot_review_common import (geometry,solve_linears,build_expected,
    decode_polynomials,input_polynomials,evaluate)

HERE=Path(__file__).resolve().parent


def normalized_elementary(label):
    return label.replace('elementary:','').replace('e2:diff:','e2:').replace(':frobenius',':square')


def main():
    windows,roles=geometry()
    manifest=json.loads((HERE/'exact_pivot_math_audit.json').read_text())
    sources=json.loads((HERE/'exact_structure_gauge_certificate.json').read_text())['boards']
    reports=[]
    for variant in manifest['exports']:
        name=variant['name']
        pivots=variant['pivots']
        assert len(pivots)==len(set(pivots))==4
        assert max(len(set(window)&set(pivots)) for window in windows)==1
        substitutions=solve_linears(list(roles.values()),pivots)
        free=[cell for cell in range(100) if cell not in pivots]
        index={cell:i for i,cell in enumerate(free)}
        forms={cell:{index[source] for source in substitutions.get(cell,{cell})} for cell in range(100)}
        domains,moments,elementary,vanished=build_expected(forms,True)
        expected_pivots={f'pivot_domain:{p}':domains[f'domain:{p}'] for p in pivots}
        assert all(not domains[f'domain:{cell}'] for cell in free)
        for label,cells in roles.items():
            total=set()
            for cell in cells:total ^= forms[cell]
            assert not total
        equations_by_mode={}
        files=[]
        for count in (40,80):
            path=HERE/f'exact_pivot_math_{name}_fourier{count}.json'
            model=json.loads(path.read_text())
            assert model['coefficient_field']=='F2' and model['ring_type']=='ordinary polynomial ring'
            assert model['variables']==96 and model['free_original_cells']==free
            assert model['pivot_cells']==pivots
            assert model['pivot_substitutions']=={str(k):sorted(v) for k,v in substitutions.items()}
            assert model['count_divisor']==model['count_multiplier']==1
            assert model['symmetry_normalization'] is False and model['prefix']==''
            assert model['full_moment_count']==count
            selected={label:p for label,p in moments.items() if count==80 or
                next(e for e in map(int,label.split(':')[1].split(',')) if e)==1}
            expected=dict(selected,**expected_pivots)
            decoded=decode_polynomials(model['remaining_equations'],96,2,2)
            assert decoded==expected, (name,count)
            assert len(selected)==(36 if count==40 else 72)
            first=[{(i,i,i),()} for i in range(96)]
            wanted=first+[expected[equation['label']] for equation in model['remaining_equations']]
            text=path.with_suffix('.ms').read_text()
            assert input_polynomials(text,96)==wanted
            equations_by_mode[count]=wanted
            files.append(dict(file=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                              input_sha256=hashlib.sha256(text.encode()).hexdigest()))
        elementary_path=HERE/f'exact_pivot_math_{name}_elementary.json'
        extra=json.loads(elementary_path.read_text())
        assert extra['free_original_cells']==free and extra['pivot_cells']==pivots
        assert extra['pivot_substitutions']=={str(k):sorted(v) for k,v in substitutions.items()}
        assert extra['augmentation_only'] is True and extra['count_divisor']==extra['count_multiplier']==1
        decoded=decode_polynomials(extra['remaining_equations'],96,2,2)
        assert {normalized_elementary(label):p for label,p in decoded.items()}==elementary
        tail=[elementary[normalized_elementary(equation['label'])] for equation in extra['remaining_equations']]
        for count in (40,80):
            path=HERE/f'exact_pivot_math_{name}_fourier{count}_e2.ms'
            text=path.read_text()
            assert input_polynomials(text,96)==equations_by_mode[count]+tail
            files.append(dict(file=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
        for entry in sources:
            values=[int(c)+1 for c in entry['flat']]
            assert len({tuple(values[cell] for cell in w) for w in windows})==81
            recovered=values[:]
            for p,support in substitutions.items():
                value=0
                for cell in support:value ^= values[cell]
                recovered[p]=value
            assert recovered==values
        # Actual constraints evaluated independently on five saved witnesses.
        for entry in sources[:5]:
            values=[int(entry['flat'][cell])+1 for cell in free]
            assert all(evaluate(p,values)==0 for p in list(expected_pivots.values())+
                       list(moments.values())+list(elementary.values()))
        reports.append(dict(name=name,pivots=pivots,free_variables=96,
            substitution_lengths=[len(substitutions[p]) for p in pivots],
            substituted_domain_terms=[len(expected_pivots[f'pivot_domain:{p}']) for p in pivots],
            all_moment_terms=sum(map(len,moments.values())),
            elementary_term_counts=list(map(len,elementary.values())),
            zero_unary_moments=vanished,free_domains_retained=96,pivot_domains_retained=4,
            json_models_checked=3,complete_inputs_checked=4,
            known_board_roundtrips=len(sources),known_board_equation_checks=5,
            count_divisor=1,count_multiplier=1,files=files))
    result=dict(status='PASS',variants=reports,solver_runs=0,full_count_status='NOT_COMPUTED',
                method='fresh row-index geometry, set Gaussian elimination, tuple-polynomial expansion modulo retained free cubics')
    (HERE/'exact_pivot_review_original_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({**result,'variants':[{k:v for k,v in report.items() if k!='files'} for report in reports]},indent=2))


if __name__=='__main__':main()
