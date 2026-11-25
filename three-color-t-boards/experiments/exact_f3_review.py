#!/usr/bin/env python3
"""Independent ordinary-polynomial and quotient-scope review of the F3 model.

This uses tuple monomials, reconstructs row-index geometry, solves the linear
relations afresh, and reduces only after expanding each whole moment. No solver.
"""
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib
import json
import random
import re

HERE=Path(__file__).resolve().parent


def add(a,b,scale=1):
    answer=dict(a)
    for term,c in b.items():
        value=(answer.get(term,0)+scale*c)%3
        if value:answer[term]=value
        else:answer.pop(term,None)
    return answer


def multiply(a,b):
    answer={}
    for x,c in a.items():
        for y,d in b.items():
            term=tuple(sorted(x+y))
            value=(answer.get(term,0)+c*d)%3
            if value:answer[term]=value
            else:answer.pop(term,None)
    return answer


@lru_cache(maxsize=300000)
def reduce_term(term):
    # x^3=x: positive powers reduce to1 or2, never to the constant1.
    return tuple(v for v,e in sorted(Counter(term).items()) for _ in range(2 if e%2==0 else 1))


def reduce_fields(polynomial):
    answer={}
    for term,c in polynomial.items():
        target=reduce_term(term)
        value=(answer.get(target,0)+c)%3
        if value:answer[target]=value
        else:answer.pop(target,None)
    return answer


def decode(equations):
    answer={}
    for equation in equations:
        label=equation['label'];assert label not in answer
        polynomial={}
        for c,encoded in equation['terms']:
            assert type(c) is int and c in (1,2)
            word=int(encoded,16);assert 0<=word<1<<(4*96)
            term=tuple(i for i in range(96) for _ in range((word>>(4*i))&15))
            assert term not in polynomial
            polynomial[term]=c
        assert polynomial
        answer[label]=polynomial
    return answer


def evaluate(polynomial,values):
    answer=0
    for term,c in polynomial.items():
        value=c
        for i in term:value=value*values[i]%3
        answer=(answer+value)%3
    return answer


def parse_input(text):
    lines=text.splitlines()
    assert lines[0]==','.join(f'x{i+1}' for i in range(96)) and lines[1]=='3'
    polynomials=[]
    for expression in ''.join(lines[2:]).split(','):
        polynomial={}
        for summand in expression.split('+'):
            coefficient=1;term=[]
            for factor in summand.split('*'):
                if factor.isdecimal():coefficient=coefficient*int(factor)%3
                else:
                    match=re.fullmatch(r'x([1-9][0-9]*)(?:\^([1-9][0-9]*))?',factor)
                    assert match,factor
                    variable=int(match[1])-1;power=int(match[2] or '1')
                    assert 0<=variable<96 and power<=3
                    term += [variable]*power
            term=tuple(sorted(term));assert term not in polynomial and coefficient
            polynomial[term]=coefficient
        polynomials.append(polynomial)
    return polynomials


def main():
    source=HERE/'exact_f3_math_model.json';data=json.loads(source.read_text())
    windows=[((r-1)**2+j-1,r*r+j-1,r*r+j,r*r+j+1)
             for r in range(1,10) for j in range(1,2*r)]
    assert len(windows)==len(set(windows))==81
    roles=[{w[k] for w in windows} for k in range(4)]
    assert all(len(role)==81 for role in roles)
    order=data['original_cell_order'];assert sorted(order)==list(range(100))
    groups=data['signature_group_order']
    signatures={i:''.join(str(int(i in r)) for r in roles) for i in range(100)}
    assert set(signatures.values())==set(groups) and len(groups)==12
    assert order==sorted(range(100),key=lambda i:(groups.index(signatures[i]),i))
    assert set(order[:81])==roles[0]
    # Geometry gives the signed unary equations before any supplied substitution.
    rows=[]
    for role in roles:
        row={}
        for position,cell in enumerate(order):
            if cell in role:
                row=add(row,{position:1})
                if position:row=add(row,{position-1:2})
        rows.append(row)
    assert [{str(k):v for k,v in row.items()} for row in rows]==data['unary_equations_before_elimination']
    pivots=data['eliminated_prefix_variables'];assert len(pivots)==len(set(pivots))==4
    for i,pivot in enumerate(pivots):
        j=next(j for j in range(i,4) if rows[j].get(pivot,0))
        rows[i],rows[j]=rows[j],rows[i]
        inv=pow(rows[i][pivot],-1,3)
        rows[i]={v:c*inv%3 for v,c in rows[i].items()}
        for j in range(4):
            if j!=i:rows[j]=add(rows[j],rows[i],-rows[j].get(pivot,0))
    substitutions={pivot:{v:-c%3 for v,c in row.items() if v!=pivot}
                   for pivot,row in zip(pivots,rows)}
    assert {str(k):{str(v):c for v,c in f.items()} for k,f in substitutions.items()}==data['prefix_variable_substitutions']
    assert all(not(set(f)&set(pivots)) for f in substitutions.values())
    free=[i for i in range(100) if i not in pivots];assert free==data['free_prefix_variables']
    indices={v:i for i,v in enumerate(free)}
    ys={v:{(indices[i],):c for i,c in substitutions.get(v,{v:1}).items()} for v in range(100)}
    forms={cell:add(ys[j],ys.get(j-1,{}),-1) for j,cell in enumerate(order)}
    declared_forms={int(cell):{(int(v),):c for v,c in form.items()}
                    for cell,form in data['original_color_linear_forms'].items()}
    assert forms==declared_forms
    cumulative={}
    for j,cell in enumerate(order):
        cumulative=add(cumulative,forms[cell]);assert cumulative==ys[j]
    domains={f'field:{i}':{(i,i,i):1,(i,):2} for i in range(96)}
    assert domains==decode(data['domain_equations'])
    # Explicit ordinary-polynomial identity L^3-L = sum c_i(x_i^3-x_i).
    # This establishes that no substituted original/pivot domains are lost.
    for form in list(forms.values())+list(ys.values()):
        actual=add(multiply(multiply(form,form),form),form,-1)
        expected={}
        for (i,),c in form.items():expected=add(expected,domains[f'field:{i}'],c)
        assert actual==expected
    powers={cell:({():1},form,multiply(form,form)) for cell,form in forms.items()}
    moments={};vanished=[]
    for exponents in product(range(3),repeat=4):
        if not any(exponents):continue
        poly={():2} if exponents==(2,2,2,2) else {}
        for window in windows:
            term={():1}
            for cell,exponent in zip(window,exponents):term=multiply(term,powers[cell][exponent])
            poly=add(poly,term)
        poly=reduce_fields(poly)
        label='moment:'+','.join(map(str,exponents))
        if poly:moments[label]=poly
        else:vanished.append(exponents)
    assert len(moments)==76 and vanished==[tuple(e) for e in data['eliminated_linear_moments']]
    assert moments==decode(data['moment_equations'])
    assert sum(map(len,moments.values()))==96050
    for eq in data['moment_equations']:
        e=eq['original_role_exponents']
        assert eq['label']=='moment:'+','.join(map(str,e))
        assert eq['target_already_subtracted'] is True and eq['target_moment']==int(e==[2,2,2,2])
    text=(HERE/'exact_f3_math_model.ms').read_text()
    assert parse_input(text)==list(domains.values())+list(moments.values())
    # Direct inverse of the color evaluation transform via indicators.
    for color in range(3):
        for value in range(3):assert (1-(value-color)**2)%3==int(value==color)
    vandermonde=[[pow(color,e,3) for color in range(3)] for e in range(3)]
    determinant=(vandermonde[0][0]*(vandermonde[1][1]*vandermonde[2][2]-vandermonde[1][2]*vandermonde[2][1])
                -vandermonde[0][1]*(vandermonde[1][0]*vandermonde[2][2]-vandermonde[1][2]*vandermonde[2][0])
                +vandermonde[0][2]*(vandermonde[1][0]*vandermonde[2][1]-vandermonde[1][1]*vandermonde[2][0]))%3
    assert determinant==2
    for exponents in product(range(3),repeat=4):
        expected=1
        for e in exponents:expected=expected*sum(pow(c,e,3) for c in range(3))%3
        assert expected==int(exponents==(2,2,2,2))
    rng=random.Random(0xF3A0D17)
    for _ in range(12):
        values=[rng.randrange(3) for _ in free]
        board=[evaluate(forms[c],values) for c in range(100)]
        for label,poly in moments.items():
            exponents=tuple(map(int,label.split(':')[1].split(',')))
            direct=0
            for w in windows:
                value=1
                for c,e in zip(w,exponents):value=value*pow(board[c],e,3)%3
                direct=(direct+value)%3
            assert evaluate(poly,values)==(direct-int(exponents==(2,2,2,2)))%3
    witnesses=json.loads((HERE/'exact_structure_gauge_certificate.json').read_text())['boards']
    witness_hashes=[]
    for witness in witnesses:
        flat=witness['flat'];board=list(map(int,flat))
        assert len({tuple(board[c] for c in w) for w in windows})==81
        prefix=[];value=0
        for cell in order:value=(value+board[cell])%3;prefix.append(value)
        values=[prefix[v] for v in free]
        assert all(evaluate(forms[c],values)==board[c] for c in range(100))
        witness_hashes.append(hashlib.sha256(flat.encode()).hexdigest())
    invalid=json.loads((HERE/'exact_structure_counterexample.json').read_text())
    board=list(map(int,''.join(invalid['rows'])));prefix=[];value=0
    for cell in order:value=(value+board[cell])%3;prefix.append(value)
    values=[prefix[v] for v in free]
    assert all(evaluate(forms[c],values)==board[c] for c in range(100))
    failed=[label for label,poly in moments.items() if evaluate(poly,values)]
    assert failed
    from exact_msolve_backend import definitions
    actual,metadata=definitions(prime=3,ternary_native_field=True)
    assert actual==text and metadata['count_divisor']==metadata['count_multiplier']==1
    assert metadata['field']=='F3' and metadata['prefix']=='' and metadata['fixed_original_cells']==[]
    assert metadata['extension_variable'] is False and metadata['symmetry_normalization'] is False
    report=dict(status='PASS',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        input_sha256=hashlib.sha256(text.encode()).hexdigest(),
        independent_geometry='row-index formula for all81 placements',linear_relations_rank=4,
        complete_polynomials_compared=172,retained_moment_terms=96050,
        ordinary_field_ideal_identities_checked=200,
        reduction='expand whole moment ordinarily, then reduce positive exponents modulo x^3-x',
        vandermonde_determinant_mod3=determinant,random_free_assignments=12,
        existing_valid_boards_roundtripped=len(witness_hashes),witness_sha256=witness_hashes,
        uniform_triple_counterexample_failed_moments=failed,
        backend_input_identical=True,count_divisor=1,count_multiplier=1,
        full_count_status='NOT_COMPUTED',solver_runs=0)
    (HERE/'exact_f3_review_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='witness_sha256'},indent=2))


if __name__=='__main__':main()
