#!/usr/bin/env python3
"""Compare reduced msolve input with fresh full geometry; never run a solver."""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import re
import tempfile

HERE=Path(__file__).resolve().parent
PIVOTS=(0,81,90,99)
FREE=tuple(cell for cell in range(100) if cell not in PIVOTS)
FREE_INDEX={cell:i for i,cell in enumerate(FREE)}
POINTS={(r,x):r*r+r+x for r in range(10) for x in range(-r,r+1)}
WINDOWS=tuple((POINTS[r,x],POINTS[r+1,x-1],POINTS[r+1,x],POINTS[r+1,x+1])
              for r in range(9) for x in range(-r,r+1))


def toggle(terms,term):
    if term in terms:terms.remove(term)
    else:terms.add(term)


def term(pairs):
    powers=Counter()
    for cell,power in pairs:powers[cell]+=power
    return tuple(sorted((cell,power%3) for cell,power in powers.items() if power%3))


def substitutions():
    # Gaussian elimination of the four unary sums directly from geometry.
    rows=[sum(1<<window[role] for window in WINDOWS) for role in range(4)]
    for i,cell in enumerate(PIVOTS):
        j=next(j for j in range(i,4) if rows[j]>>cell&1)
        rows[i],rows[j]=rows[j],rows[i]
        for j in range(4):
            if j!=i and rows[j]>>cell&1:rows[j]^=rows[i]
    result={}
    for cell,row in zip(PIVOTS,rows):
        row^=1<<cell
        assert all(not row>>pivot&1 for pivot in PIVOTS)
        result[cell]=tuple(c for c in FREE if row>>c&1)
    assert [len(result[c]) for c in PIVOTS]==[80,17,80,17]
    return result


def fresh_reduction():
    sources=substitutions()
    assert max(sum(cell in PIVOTS for cell in window) for window in WINDOWS)==1
    moments={};zero=[]
    for e in product(range(3),repeat=4):
        if not any(e):continue
        polynomial=set()
        for window in WINDOWS:
            fixed=[];pivot=None
            for cell,power in zip(window,e):
                if not power:continue
                if cell in PIVOTS:
                    assert pivot is None;pivot=(cell,power)
                else:fixed.append((cell,power))
            if pivot is None:toggle(polynomial,term(fixed))
            else:
                cell,power=pivot
                # In F2, a substituted square is the sum of source squares.
                for source in sources[cell]:toggle(polynomial,term(fixed+[(source,power)]))
        if polynomial:moments[e]=frozenset(polynomial)
        else:zero.append(e)
    assert len(moments)==72 and len(zero)==8
    assert all(sum(power!=0 for power in e)==1 for e in zero)
    cubes={}
    for cell in PIVOTS:
        polynomial={()}
        for a in sources[cell]:
            for b in sources[cell]:toggle(polynomial,term(((a,1),(b,2))))
        cubes[cell]=frozenset(polynomial)
    assert [len(cubes[c]) for c in PIVOTS]==[6321,272,6321,272]
    return sources,moments,zero,cubes


def parse_input(path):
    raw=path.read_bytes();lines=raw.decode().splitlines()
    assert lines[0]==','.join(f'x{i+1}' for i in range(96))
    assert lines[1]=='2'
    polynomials='\n'.join(lines[2:]).strip().split(',\n')
    assert polynomials[:96] in ([f'x{i+1}^3-1' for i in range(96)],
                               [f'x{i+1}^3+1' for i in range(96)])
    result=[]
    for expression in polynomials[96:]:
        polynomial=set()
        for summand in expression.split('+'):
            factors=summand.split('*')
            if factors[0]=='1':factors.pop(0)
            pairs=[]
            for factor in factors:
                match=re.fullmatch(r'x([1-9][0-9]*)(?:\^([12]))?',factor)
                assert match,factor
                variable=int(match[1])-1
                assert 0<=variable<96
                pairs.append((FREE[variable],int(match[2] or 1)))
            assert len({cell for cell,_ in pairs})==len(pairs)
            toggle(polynomial,term(pairs))
        result.append(frozenset(polynomial))
    return result,hashlib.sha256(raw).hexdigest(),len(polynomials)


def main():
    sources,moments,zero,cubes=fresh_reduction()
    representative={e:p for e,p in moments.items() if next(v for v in e if v)==1}
    assert len(representative)==36
    for e,p in representative.items():
        conjugate=frozenset(term((cell,2*power) for cell,power in t) for t in p)
        assert conjugate==moments[tuple(2*v%3 for v in e)]
    reports=[];parsed_modes={}
    for mode in (40,80):
        path=HERE/f'exact_msolve_reduced_{mode}.ms'
        actual,digest,generators=parse_input(path)
        parsed_modes[mode]=actual
        expected=list(representative.values())+list(cubes.values())
        if mode==80:
            expected += [moments[tuple(2*v%3 for v in e)] for e in representative]
        assert Counter(actual)==Counter(expected)
        assert generators==(136 if mode==40 else 172)
        report={'mode':mode,'input_file':path.name,'input_sha256':digest,
                'variables':96,'ordinary_free_cubic_domains':96,
                'retained_pivot_cubic_domains':4,
                'nonzero_reduced_moments':36 if mode==40 else 72,
                'generators':generators,'remaining_polynomial_terms':sum(map(len,actual)),
                'all_polynomials_match_fresh_geometric_substitution':True}
        metadata_path=path.with_suffix('.json')
        if metadata_path.exists():
            metadata=json.loads(metadata_path.read_text())
            assert metadata['variables']==96 and metadata['prime']==2
            assert metadata['ring_type']=='ordinary polynomial ring'
            assert metadata['count_scope']=='full labeled boards'
            assert metadata['prefix']=='' and metadata['fixed_cell_count']==0
            assert metadata['symmetry_normalization'] is False and metadata['extension_variable'] is False
            assert metadata['count_divisor']==metadata['count_multiplier']==1
            assert metadata['free_original_cells']==list(FREE)
            assert metadata['eliminated_original_cells']==list(PIVOTS)
            assert metadata['input_sha256']==digest
            report['helper_metadata_scope_verified']=True
            report['reduced_source_sha256']=metadata['source_sha256']
        reports.append(report)
    assert parsed_modes[80][:40]==parsed_modes[40]
    # Exercise the actual adapter path only in preparation mode.
    import exact_msolve_backend as adapter
    adapter_checks=[]
    with tempfile.TemporaryDirectory(prefix='exact_reduced_input_audit_') as directory:
        for mode,selection in ((40,'representatives'),(80,'all')):
            text,metadata=adapter.definitions(prime=2,ternary_reduced=selection)
            assert text==(HERE/f'exact_msolve_reduced_{mode}.ms').read_text()
            assert metadata['reduced_source_sha256']==reports[0]['reduced_source_sha256']
            assert metadata['generator_sha256']==hashlib.sha256((HERE/'exact_msolve_reduced.py').read_bytes()).hexdigest()
            output=Path(directory)/str(mode)
            prepared=adapter.run(output,prime=2,ternary_reduced=selection,prepare_only=True)
            assert prepared['status']=='PREPARED_NOT_RUN' and prepared['basis_complete'] is False
            assert prepared['source_sha256']==hashlib.sha256(text.encode()).hexdigest()
            assert prepared['reduced_source_sha256']==metadata['reduced_source_sha256']
            assert prepared['count_divisor']==prepared['count_multiplier']==1
            assert output.with_suffix('.ms').read_text()==text
            adapter_checks.append({'mode':mode,'byte_identical_to_helper':True,
                                   'prepare_only_path_passed':True,'input_and_reduced_source_hashes_distinct':True})
    for kwargs in ({'prime':29},{'prefix':'0'},{'binary':True},{'fixture':'domain'},
                   {'pivot_order':True},{'ternary_reduced':'invalid'}):
        args={'prime':2,'ternary_reduced':'all'};args.update(kwargs)
        try:adapter.definitions(**args)
        except ValueError:pass
        else:raise AssertionError(('unsupported adapter combination accepted',args))
    report={'status':'PASS','scope':'unrestricted labeled ten-row ternary boards',
            'prime':2,'count_multiplier':1,'count_divisor':1,
            'eliminated_original_cells':list(PIVOTS),'free_original_cells':list(FREE),
            'fresh_substitution_lengths':{cell:len(src) for cell,src in sources.items()},
            'eight_original_moments_reducing_to_zero':[list(e) for e in zero],
            'retained_pivot_cube_term_counts':{cell:len(p) for cell,p in cubes.items()},
            'cases':reports,'all80_preserves_default40_polynomial_prefix':True,
            'adapter_checks':adapter_checks,'unsupported_adapter_combinations_rejected':6,
            'adapter_sha256':hashlib.sha256(Path(adapter.__file__).read_bytes()).hexdigest(),
            'solver_invoked':False,'full_count_evaluated':False}
    (HERE/'exact_parity_math_reduced_input_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='free_original_cells'},indent=2))


if __name__=='__main__':
    main()
