#!/usr/bin/env python3
"""Independent ordinary-polynomial audit of sparse prefix e4 constraints."""
from itertools import combinations
from pathlib import Path
import hashlib
import json

from exact_pivot_review_common import (geometry,solve_linears,multiply,square,
    decode_polynomials,evaluate)

HERE=Path(__file__).resolve().parent


def coefficients(forms):
    """Balanced product tree, truncated in the formal parameter at degree4."""
    if not forms:
        return [{()},set(),set(),set(),set()]
    if len(forms)==1:
        return [{()},forms[0],set(),set(),set()]
    middle=len(forms)//2
    left,right=coefficients(forms[:middle]),coefficients(forms[middle:])
    result=[set() for _ in range(5)]
    for degree in range(5):
        for i in range(degree+1):
            result[degree] ^= multiply(left[i],right[degree-i])
    return result


def main():
    model_path=HERE/'exact_msolve_elementary_analysis_prefix_gray_model.json'
    source_path=HERE/'exact_pivot_math_prefix_e4_constraints.json'
    model=json.loads(model_path.read_text());source=json.loads(source_path.read_text())
    assert hashlib.sha256(model_path.read_bytes()).hexdigest()==source['prefix_source_sha256']
    assert source['format']=='t-board-prefix-e4-augmentation-v1'
    assert source['variables']==96 and source['coefficient_characteristic']==2
    assert source['ring_type']=='ordinary polynomial ring' and source['augmentation_only'] is True
    assert source['count_divisor']==source['count_multiplier']==1
    assert source['prefix']=='' and source['symmetry_normalization'] is False
    assert source['free_prefix_variables']==model['free_prefix_variables']
    assert source['original_cell_order']==model['original_cell_order']
    assert source['required_e2_labels']==['e2:T','e2:T:M','e2:M:L','e2:M:R']
    _,roles=geometry();order=model['original_cell_order'];free=model['free_prefix_variables']
    index={v:i for i,v in enumerate(free)}
    unary=[]
    for cells in roles.values():
        row=set()
        for j,cell in enumerate(order):
            if cell in cells:
                row ^= {j}
                if j:row ^= {j-1}
        unary.append(row)
    replacements=solve_linears(unary,model['eliminated_prefix_variables'])
    yforms=[{(index[v],) for v in replacements.get(i,{i})} for i in range(100)]
    forms={cell:yforms[j]^(yforms[j-1] if j else set()) for j,cell in enumerate(order)}
    def sym(cells):return coefficients([forms[cell] for cell in order if cell in cells])
    full={label:sym(cells) for label,cells in roles.items()}
    assert all(not row[1] for row in full.values())
    expected={'e4:T':full['T'][4]}
    certificates=[]
    for a,b in (('T','M'),('M','L'),('M','R')):
        A,B=roles[a],roles[b];C,D,E=A&B,A-B,B-A
        common,left,right=sym(C),sym(D),sym(E)
        s=common[1]
        assert left[1]==right[1]==s and len(D)==len(E)
        boundary=left[4]^right[4]
        domain_sum=set()
        for cell in D|E:
            domain_sum ^= multiply(forms[cell],square(forms[cell]))^{()}
        difference=full[a][4]^full[b][4]^boundary
        correction=multiply(square(s)^common[2],full[a][2]^full[b][2])^multiply(s,domain_sum)
        assert difference==correction
        assert correction, 'correction must not be silently dropped as an identity'
        # Independently verify Newton's degree3 identity that gives this certificate.
        for cells,elementary in ((D,left),(E,right)):
            cubes=set()
            for cell in cells:cubes ^= multiply(forms[cell],square(forms[cell]))
            assert cubes==(multiply(elementary[1],square(elementary[1]))^
                multiply(elementary[1],elementary[2])^elementary[3])
        expected[f'e4:{a}:{b}']=boundary
        certificates.append(dict(roles=[a,b],exclusive_set_size=len(D),
            exact_polynomial_identity=True,correction_terms=len(correction),
            required_generators=['existing unary elimination','role e2 equations','original transformed cubic domains']))
    decoded=decode_polynomials(source['equations'],96,4,4)
    assert decoded==expected and sum(map(len,decoded.values()))==14194
    assert all(len(term)==4 for polynomial in decoded.values() for term in polynomial)
    # Independent verification of the optional sparse top-path formula.
    interior=yforms[:80]
    assert all(len(p)==1 for p in interior)
    atoms=[square(p) for p in interior]+[multiply(a,b) for a,b in zip(interior,interior[1:])]
    top=set()
    for a,b in combinations(atoms,2):top ^= multiply(a,b)
    for a,b in zip(interior,interior[1:]):
        top ^= multiply(square(a),square(b))
        top ^= multiply(multiply(a,square(a)),b)
        top ^= multiply(a,multiply(b,square(b)))
    assert top==decoded['e4:T']
    seeds=json.loads((HERE.parent/'sources/anc/certificates.json').read_text())['ternary_seeds']
    for rows in seeds:
        z=[int(c)+1 for c in ''.join(rows)];y=[];value=0
        for cell in order:value ^= z[cell];y.append(value)
        values=[y[v] for v in free]
        assert all(evaluate(p,values)==0 for p in decoded.values())
    report=dict(status='PASS',solver_runs=0,source_sha256=hashlib.sha256(source_path.read_bytes()).hexdigest(),
        prefix_source_sha256=source['prefix_source_sha256'],
        independent_method='balanced formal-parameter product tree and ordinary tuple monomials',
        term_counts={label:len(poly) for label,poly in decoded.items()},
        raw_role_e4_term_counts={label:len(row[4]) for label,row in full.items()},
        ordinary_degree_four_only=True,no_exponent_reduction=True,
        role_difference_certificates=certificates,newton_degree3_identities_checked=6,
        top_path_formula_checked=True,valid_boards_checked=len(seeds),
        histogram_implication='Together with e1/e2, e4=0 forces each role color count congruent3 modulo8.',
        full_count_status='NOT_COMPUTED')
    (HERE/'exact_pivot_review_e4_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
