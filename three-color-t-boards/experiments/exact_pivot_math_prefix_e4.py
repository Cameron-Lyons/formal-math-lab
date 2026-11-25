#!/usr/bin/env python3
"""Check sparse prefix e4 and role differences; no solver or model mutation."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import argparse
import hashlib
import json

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'exact_msolve_elementary_analysis_prefix_gray_model.json'
SOURCE_SHA256='7f8251ab52e8d6869c19cc861dc98b0c1e66904313b0d87920d9f95659700092'
MUL=((0,0,0,0),(0,1,2,3),(0,2,3,1),(0,3,1,2))


def mul(a,b):
    out=set()
    for x in a:
        for y in b:
            z=x+y # four-bit ordinary exponents; total degree never exceeds4
            if z in out:out.remove(z)
            else:out.add(z)
    return out


def elementary(linears,degree=4):
    coeff=[{0}]+[set() for _ in range(degree)]
    for linear in linears:
        for k in range(degree,0,-1):coeff[k]^=mul(coeff[k-1],linear)
    return coeff


def degree(term):
    result=0
    while term:
        result+=term&15;term>>=4
    return result


def tiny_field_check():
    checked=0;zero_e2=0
    for n in range(1,9):
        for z in product((1,2,3),repeat=n):
            coeff=[1,0,0,0,0]
            p=[0];w=[0];rhs=0
            for i,value in enumerate(z,1):
                delta=MUL[value][p[-1]]
                rhs^=MUL[delta][MUL[p[-1]][p[-1]]^w[-1]]
                if i%2==0:rhs^=value
                p.append(p[-1]^value);w.append(w[-1]^delta)
                for k in range(4,0,-1):coeff[k]^=MUL[value][coeff[k-1]]
            assert rhs==coeff[4] and w[-1]==coeff[2]
            if w[-1]==0:
                zero_e2+=1
                short=0
                for i,value in enumerate(z,1):
                    if i%2==0:short^=value
                for i in range(1,n):
                    short^=MUL[w[i]][MUL[z[i-1]][z[i-1]]]
                    short^=MUL[w[i]][w[i-1]]^MUL[w[i]][w[i]]
                assert short==coeff[4]
            checked+=1
    assert checked==9840
    return {'all_nonzero_F4_sequences_length1_through8':checked,
            'zero_final_e2_sequences_checked':zero_e2,
            'general_and_short_carry_identities_match_direct_e4':True}


def build():
    raw=SOURCE.read_bytes();model=json.loads(raw)
    assert hashlib.sha256(raw).hexdigest()==SOURCE_SHA256
    order=model['original_cell_order'];assert sorted(order)==list(range(100))
    free=model['free_prefix_variables'];index={p:i for i,p in enumerate(free)}
    substitutions={int(k):v for k,v in model['prefix_variable_substitutions'].items()}
    prefix=[]
    for i in range(100):prefix.append({1<<(4*index[j]) for j in substitutions.get(i,[i])})
    forms={}
    for position,cell in enumerate(order):
        forms[cell]=prefix[position]^(prefix[position-1] if position else set())
        expected={1<<(4*index[j]) for j in model['original_color_linear_forms'][str(cell)]}
        assert forms[cell]==expected
    windows=[((r-1)**2+j,r*r+j,r*r+j+1,r*r+j+2)
             for r in range(1,10) for j in range(2*r-1)]
    role_sets=[{w[i] for w in windows} for i in range(4)]
    assert set(order[:81])==role_sets[0]
    def sym(cells):return elementary([forms[c] for c in order if c in cells])
    role=[sym(cells) for cells in role_sets]
    assert all(not c[1] for c in role)
    elementary_expected=[role[0][2],role[0][2]^role[2][2],role[2][2]^role[1][2],role[2][2]^role[3][2]]
    assert elementary_expected==[{int(t,16) for t in e['terms']} for e in model['elementary_equations'][:4]]

    # Pure ordinary-polynomial path identity; no domain equations are used.
    interior=[next(iter(p)) for p in prefix[:80]]
    assert all(len(p)==1 for p in prefix[:80]) and len(set(interior))==80
    atoms=[2*p for p in interior]+[a+b for a,b in zip(interior,interior[1:])]
    path_e4=set()
    for a,b in combinations(atoms,2):
        t=a+b
        if t in path_e4:path_e4.remove(t)
        else:path_e4.add(t)
    for a,b in zip(interior,interior[1:]):
        path_e4.symmetric_difference_update((2*a+2*b,3*a+b,a+3*b))
    assert path_e4==role[0][4] and len(path_e4)==12324

    certificates=[]
    sparse=[('e4:T',role[0][4])]
    for a,b in ((0,2),(2,1),(2,3)):
        A,B=role_sets[a],role_sets[b]
        C,D,E=A&B,A-B,B-A
        common,left,right=sym(C),sym(D),sym(E)
        assert len(D)==len(E) and left[1]==right[1]==common[1]
        s=common[1]
        correction=mul({2*t for t in s}^common[2],role[a][2]^role[b][2])
        domains=set()
        for c in D|E:
            domains^=mul(forms[c],{2*t for t in forms[c]})^{0}
        correction^=mul(s,domains)
        boundary=left[4]^right[4]
        assert role[a][4]^role[b][4]^boundary==correction
        label='e4:'+('T','L','M','R')[a]+':'+('T','L','M','R')[b]
        sparse.append((label,boundary))
        certificates.append({'roles':[a,b],'exclusive_sizes':[len(D),len(E)],
                             'boundary_e4_terms':len(boundary),
                             'full_role_e4_difference_terms':len(role[a][4]^role[b][4]),
                             'ordinary_ideal_identity_verified':True})

    def pure_fourths(poly):
        return sum(t!=0 and (t & (t-1))==0 and t.bit_length()%4==3 for t in poly)
    document={
        'format':'t-board-prefix-e4-augmentation-v1',
        'coefficient_characteristic':2,'variables':96,
        'ring_type':'ordinary polynomial ring',
        'scope':'full labeled ternary boards','augmentation_only':True,
        'prefix_source':SOURCE.name,'prefix_source_sha256':SOURCE_SHA256,
        'original_cell_order':order,'free_prefix_variables':free,
        'required_base':'retain the exact prefix Fourier model, all100 transformed original-cell cubics, and all4 role e2 conditions; unary equations remain enforced by the coordinate map',
        'required_e2_labels':['e2:T','e2:T:M','e2:M:L','e2:M:R'],
        'monomial_encoding':'hex integer: exponent of free variable i in bits4*i..4*i+3; ordinary exponents; coefficient1',
        'equations':[{'label':label,'terms':[hex(t) for t in sorted(p)]} for label,p in sparse],
        'frobenius_partners_included':False,'term_count':sum(len(p) for _,p in sparse),
        'prefix':'','symmetry_normalization':False,'count_divisor':1,'count_multiplier':1,
        'full_count_status':'UNEVALUATED; no solver run',
    }
    assert document['term_count']==14194
    audit={
        'status':'PASS','scope':'symbolic e4 support and ideal identities; no solver or input model change',
        'prefix_source':SOURCE.name,'prefix_source_sha256':hashlib.sha256(raw).hexdigest(),
        'coordinate_forms_reconstructed_exactly':True,
        'raw_role_e4_terms':dict(zip(('T','L','M','R'),[len(c[4]) for c in role])),
        'sparse_equation_terms':{label:len(p) for label,p in sparse},
        'sparse_ordinary_degree_histograms':{label:{str(d):n for d,n in sorted(Counter(map(degree,p)).items())} for label,p in sparse},
        'pure_fourth_power_counts':{label:pure_fourths(p) for label,p in sparse},
        'top_path_formula_terms':len(path_e4),
        'role_difference_certificates':certificates,
        'cubic_lift_cost':{'new_auxiliary_variables':79,'quadratic_definitions':79,
                          'quadratic_definition_terms':315,'cubic_relation_terms':395,
                          'extra_domain_equations_needed':0},
        'tiny_field_check':tiny_field_check(),
        'full_count_status':'UNEVALUATED',
    }
    encoded=json.dumps(document,indent=2)+'\n'
    audit['augmentation_file']='exact_pivot_math_prefix_e4_constraints.json'
    audit['augmentation_sha256']=hashlib.sha256(encoded.encode()).hexdigest()
    return audit,encoded


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true')
    args=parser.parse_args();result,encoded=build();path=Path(__file__).with_suffix('.json')
    constraints=HERE/'exact_pivot_math_prefix_e4_constraints.json'
    if args.check:
        assert json.loads(path.read_text())==result
        assert constraints.read_text()==encoded
    else:
        path.write_text(json.dumps(result,indent=2)+'\n')
        constraints.write_text(encoded)
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
