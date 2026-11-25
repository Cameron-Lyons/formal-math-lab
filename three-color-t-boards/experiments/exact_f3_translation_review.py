#!/usr/bin/env python3
"""Independent audit of explicit F3 translation factorization; no solver."""
from itertools import product
from math import comb
from pathlib import Path
import hashlib
import json

from exact_f3_review import add,multiply,reduce_fields,decode,evaluate,parse_input
from exact_f3_e3_review import elementary

HERE=Path(__file__).resolve().parent


def moments(windows,forms):
    powers={c:({():1},p,multiply(p,p)) for c,p in forms.items()}
    answer={}
    for exponents in product(range(3),repeat=4):
        if not any(exponents):continue
        polynomial={():2} if exponents==(2,2,2,2) else {}
        for window in windows:
            term={():1}
            for cell,e in zip(window,exponents):term=multiply(term,powers[cell][e])
            polynomial=add(polynomial,term)
        answer[exponents]=reduce_fields(polynomial)
    return answer


def main():
    path=HERE/'exact_f3_translation_model.json';data=json.loads(path.read_text())
    e3_path=HERE/'exact_f3_translation_e3_constraints.json';e3_data=json.loads(e3_path.read_text())
    assert e3_data['source_translation_model_sha256']==hashlib.sha256(path.read_bytes()).hexdigest()
    native=json.loads((HERE/'exact_f3_math_model.json').read_text())
    assert data['source_native_model_sha256']==hashlib.sha256((HERE/'exact_f3_math_model.json').read_bytes()).hexdigest()
    windows=[((r-1)**2+j-1,r*r+j-1,r*r+j,r*r+j+1)
             for r in range(1,10) for j in range(1,2*r)]
    roles=[{w[k] for w in windows} for k in range(4)]
    order=data['original_cell_order'];assert order==native['original_cell_order']
    assert sorted(order)==list(range(100)) and order.index(0)==8
    # Solve five relations from geometry: four role sums and normalized apex0.
    rows=[]
    for role in roles:
        row={}
        for j,cell in enumerate(order):
            if cell in role:
                row=add(row,{j:1})
                if j:row=add(row,{j-1:2})
        rows.append(row)
    rows.append({8:1,7:2})
    pivots=[80,16,81,99,8]
    for i,pivot in enumerate(pivots):
        j=next(j for j in range(i,5) if rows[j].get(pivot,0))
        rows[i],rows[j]=rows[j],rows[i]
        inverse=pow(rows[i][pivot],-1,3)
        rows[i]={v:c*inverse%3 for v,c in rows[i].items()}
        for j in range(5):
            if j!=i:rows[j]=add(rows[j],rows[i],-rows[j].get(pivot,0))
    replacements={pivot:{v:-c%3 for v,c in row.items() if v!=pivot}
                  for pivot,row in zip(pivots,rows)}
    free=[i for i in range(100) if i not in pivots]
    assert len(free)==95 and free==data['free_normalized_prefix_variables']
    indices={v:i for i,v in enumerate(free)}
    prefix_forms={j:{(indices[v],):c for v,c in replacements.get(j,{j:1}).items()}
                  for j in range(100)}
    normalized={cell:add(prefix_forms[j],prefix_forms.get(j-1,{}),-1)
                for j,cell in enumerate(order)}
    assert not normalized[0]
    original={cell:add(p,{(95,):1}) for cell,p in normalized.items()}
    for key,wanted in [('normalized_prefix_linear_forms',prefix_forms),
                       ('normalized_color_linear_forms',normalized),('original_color_linear_forms',original)]:
        declared={int(c):{(int(i),):v for i,v in row.items()} for c,row in data[key].items()}
        assert declared==wanted
    assert original[0]=={(95,):1}
    # Symbolically recover all96 new coordinates from original colors.
    cumulative={}
    for j,cell in enumerate(order):
        cumulative=add(cumulative,original[cell])
        expected=add(prefix_forms[j],{(95,):(j+1)%3})
        expected={term:c for term,c in expected.items() if c}
        assert cumulative==expected
        if j in indices:assert add(cumulative,original[0],-(j+1))=={(indices[j],):1}
    domains={f'field:{i}':{(i,i,i):1,(i,):2} for i in range(96)}
    assert decode(data['domain_equations'])==domains
    for p in original.values():
        actual=add(multiply(multiply(p,p),p),p,-1);expected={}
        for (i,),c in p.items():expected=add(expected,domains[f'field:{i}'],c)
        assert actual==expected
    normalized_moments=moments(windows,normalized)
    translated_moments=moments(windows,original)
    wanted={f'moment:{",".join(map(str,e))}':p for e,p in normalized_moments.items() if p}
    assert len(wanted)==76 and sum(map(len,wanted.values()))==95490
    assert decode(data['moment_equations'])==wanted
    assert [e for e,p in normalized_moments.items() if not p]==[tuple(e) for e in native['eliminated_linear_moments']]
    # Exact binomial identities modulo retained field domains. The diagonal
    # coefficient is1, and all other terms have strictly lower total degree.
    triangular_entries=0
    for e,actual in translated_moments.items():
        expected={}
        for f in product(*(range(n+1) for n in e)):
            if not any(f):continue  # Constant moment81 and its target are0.
            coefficient=1
            for upper,lower in zip(e,f):coefficient=coefficient*comb(upper,lower)%3
            offset=sum(e)-sum(f)
            if f==e:assert coefficient==1 and offset==0
            elif coefficient:assert sum(f)<sum(e)
            for term,c in normalized_moments[f].items():
                target=term+(95,)*offset
                value=(expected.get(target,0)+coefficient*c)%3
                if value:expected[target]=value
                else:expected.pop(target,None)
            triangular_entries+=bool(coefficient)
        assert reduce_fields(expected)==actual
    role=[elementary([normalized[c] for c in sorted(cells)]) for cells in roles]
    shifted_role=[elementary([original[c] for c in sorted(cells)]) for cells in roles]
    e3={'e3:T':role[0][3]}
    for a,b in ((0,2),(2,1),(2,3)):
        left=elementary([normalized[c] for c in sorted(roles[a]-roles[b])])
        right=elementary([normalized[c] for c in sorted(roles[b]-roles[a])])
        e3['e3:'+('T','L','M','R')[a]+':'+('T','L','M','R')[b]]=add(left[3],right[3],-1)
    e3={label:reduce_fields(p) for label,p in e3.items()}
    assert decode(e3_data['equations'])==e3
    assert [len(p) for p in e3.values()]==[156,174,86,150]
    for i in range(4):
        rhs=add(add(role[i][3],multiply({(95,):1},role[i][2])),multiply({(95,95):1},role[i][1]))
        assert shifted_role[i][3]==rhs
    for poly in list(wanted.values())+list(e3.values()):
        assert all(95 not in term for term in poly)
    base_text=(HERE/'exact_f3_translation_model.ms').read_text()
    e3_text=(HERE/'exact_f3_translation_e3.ms').read_text()
    assert parse_input(base_text)==list(domains.values())+list(wanted.values())
    assert parse_input(e3_text)==list(domains.values())+list(wanted.values())+list(e3.values())
    assert e3_text.startswith(base_text.rstrip('\n')+',\n')
    assert sum(any(95 in term for term in p) for p in parse_input(e3_text))==1
    for doc in (data,e3_data):
        assert doc['count_divisor']==doc['count_multiplier']==1
        assert doc['prefix']=='' and doc['fixed_original_cells']==[]
        assert doc['symmetry_normalization'] is False and doc['extension_variable'] is False
        assert doc['offset_variable_index']==95 and doc['coefficient_field']=='F3'
    witnesses=json.loads((HERE/'exact_structure_gauge_certificate.json').read_text())['boards']
    for entry in witnesses:
        board=list(map(int,entry['flat']));a=board[0];d=[(v-a)%3 for v in board]
        prefix=[];s=0
        for cell in order:s=(s+d[cell])%3;prefix.append(s)
        values=[prefix[j] for j in free]+[a]
        assert all(evaluate(original[c],values)==board[c] for c in range(100))
        assert all(evaluate(p,values)==0 for p in list(wanted.values())+list(e3.values()))
    result=dict(status='PASS',model_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        e3_source_sha256=hashlib.sha256(e3_path.read_bytes()).hexdigest(),
        base_input_sha256=hashlib.sha256(base_text.encode()).hexdigest(),
        e3_input_sha256=hashlib.sha256(e3_text.encode()).hexdigest(),
        variables=96,coupled_variables=95,independent_offset_variables=1,
        independently_solved_linear_relations=5,symbolic_coordinate_inverse=True,
        original_field_domain_identities=100,normalized_moment_terms=95490,
        exact_triangular_moment_identities=80,triangular_nonzero_entries=triangular_entries,
        exact_ordinary_role_e3_shift_identities=4,e3_terms=[len(p) for p in e3.values()],
        exported_polynomials_compared=[172,176],offset_appears_only_in_own_field_domain=True,
        existing_witnesses_roundtripped_and_evaluated=len(witnesses),
        count_divisor=1,count_multiplier=1,
        count_semantics='dimension already equals3 times the normalized dimension and equals the full labeled count',
        full_count_status='NOT_COMPUTED',solver_runs=0)
    (HERE/'exact_f3_translation_review_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
