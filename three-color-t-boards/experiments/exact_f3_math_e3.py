#!/usr/bin/env python3
"""Separate natural-F3 cubic histogram augmentation; export/check, no solver."""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json

from exact_f3_math import geometry,coordinates,add_into,field_reduce,unpack,expression

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'exact_f3_math_model.json'
SOURCE_SHA256='fe1321842be3bf5bdb8ff91cd5b9c38017d542968fe27a8d5a8952e344564cc4'
ROLES=('T','L','M','R')


def ordinary_multiply(a,b):
    out={}
    for x,c in a.items():
        for y,d in b.items():add_into(out,{x+y:c*d})
    return out


def difference(a,b):
    out=a.copy();add_into(out,b,-1);return out


def elementary(linears):
    coeff=[{0:1},{},{},{}]
    for linear in linears:
        for k in range(3,0,-1):add_into(coeff[k],ordinary_multiply(coeff[k-1],linear))
    return coeff


def normalized(poly):
    out={}
    for t,c in poly.items():add_into(out,{field_reduce(t):c})
    return out


def rank(polys):
    pivots={}
    for p in polys:
        row=p.copy()
        while row:
            t=max(row)
            if t in pivots:add_into(row,pivots[t],-row[t])
            else:
                inverse=row[t]
                pivots[t]={m:inverse*c%3 for m,c in row.items()}
                break
    return len(pivots)


def multiplicity_check():
    counts=[0,0];cases=0
    for a in range(82):
        for b in range(82-a):
            histogram=(a,b,81-a-b)
            coeff=[1,0,0,0]
            for z,n in enumerate(histogram):
                for _ in range(n):
                    for k in range(3,0,-1):coeff[k]=(coeff[k]+z*coeff[k-1])%3
            low=coeff[1]==coeff[2]==0
            assert low==all(n%3==0 for n in histogram)
            stronger=low and coeff[3]==0
            assert stronger==(all(n%3==0 for n in histogram) and len({n%9 for n in histogram})==1)
            counts[0]+=low;counts[1]+=stronger;cases+=1
    assert cases==3403 and counts==[406,136]
    return {'histograms_checked':cases,'after_e1_e2':counts[0],'after_e1_e2_e3':counts[1],
            'meaning':'all three counts have one common residue0,3,or6 modulo9; exactbalance is not implied'}


def build():
    raw=SOURCE.read_bytes();assert hashlib.sha256(raw).hexdigest()==SOURCE_SHA256
    model=json.loads(raw)
    windows,roles,order=geometry();unary,replacements,free,linear=coordinates(roles,order)
    assert free==model['free_prefix_variables'] and order==model['original_cell_order']
    forms={c:{1<<(4*v):a for v,a in f.items()} for c,f in linear.items()}
    def sym(cells):return elementary([forms[c] for c in order if c in cells])
    role=[sym(cells) for cells in roles]
    source_moments={tuple(e['original_role_exponents']):{int(t,16):c for c,t in e['terms']}
                    for e in model['moment_equations']}
    for i,p in enumerate(role):
        assert not p[1]
        e=tuple(2 if j==i else 0 for j in range(4))
        assert normalized(p[2])==source_moments[e]
        power2={}
        for c in roles[i]:add_into(power2,ordinary_multiply(forms[c],forms[c]))
        assert p[2]==power2

    eqs=[('e3:T',role[0][3])];certificates=[]
    for a,b in ((0,2),(2,1),(2,3)):
        A,B=roles[a],roles[b];C,D,E=A&B,A-B,B-A
        common,left,right=sym(C),sym(D),sym(E)
        assert left[1]==right[1]
        boundary=difference(left[3],right[3])
        correction=ordinary_multiply(common[1],difference(role[a][2],role[b][2]))
        assert difference(difference(role[a][3],role[b][3]),boundary)==correction
        label=f'e3:{ROLES[a]}:{ROLES[b]}'
        eqs.append((label,boundary))
        certificates.append({'roles':[ROLES[a],ROLES[b]],'exclusive_sizes':[len(D),len(E)],
                             'ordinary_difference_identity_verified':True})
    index={p:i for i,p in enumerate(free)}
    top_prefix=[]
    for p in range(80):
        form=replacements.get(p,{p:1})
        assert len(form)==1 and list(form.values())==[1]
        top_prefix.append(1<<(4*index[next(iter(form))]))
    assert len(set(top_prefix))==80
    path={}
    for a,b in zip(top_prefix,top_prefix[1:]):
        add_into(path,{2*a+b:1,a+2*b:2})
    assert path==role[0][3] and len(path)==158
    reduced=[(label,normalized(p)) for label,p in eqs]
    low=[p for p in source_moments.values() if max(sum(e for _,e in unpack(t)) for t in p)<=3]
    before,after=rank(low),rank(low+[p for _,p in reduced])

    # Values are original color labels, not the F4 nonzero-root encoding.
    fixtures=json.loads((HERE/'exact_structure_gauge_certificate.json').read_text())['boards']
    from exact_f3_math import evaluate
    for entry in fixtures:
        z=list(map(int,entry['flat']));s=0;prefix=[]
        for c in order:s=(s+z[c])%3;prefix.append(s)
        y=[prefix[p] for p in free]
        assert all(evaluate(p,y)==0 for _,p in reduced)

    document={
        'format':'t-board-natural-f3-e3-augmentation-v1','variables':96,
        'coefficient_characteristic':3,'ring_type':'ordinary polynomial ring',
        'scope':'full labeled ternary boards','augmentation_only':True,
        'native_source':SOURCE.name,'native_source_sha256':SOURCE_SHA256,
        'free_prefix_variables':free,'original_cell_order':order,
        'required_base':'retain all96 fieldcubics and76 native power moments, including4 unary quadratics; unary linears are enforced by the coordinate map',
        'term_encoding':'[coefficient,hex_monomial], coefficient1 or2 modulo3; full zero polynomial',
        'monomial_encoding':'hex integer: exponent of free variable i in bits4*i..4*i+3',
        'moment_reduction':'only y_i^3-y_i; positive exponents remain positive',
        'equations':[{'label':label,'terms':[[c,hex(t)] for t,c in sorted(p.items())]} for label,p in reduced],
        'frobenius_partners_included':False,'prefix':'','symmetry_normalization':False,
        'count_divisor':1,'count_multiplier':1,'full_count_status':'UNEVALUATED; no solver',
    }
    encoded=json.dumps(document,indent=2)+'\n'
    audit={
        'status':'PASS','native_source_sha256':SOURCE_SHA256,
        'augmentation_file':'exact_f3_math_e3_constraints.json',
        'augmentation_sha256':hashlib.sha256(encoded.encode()).hexdigest(),
        'raw_role_e3_terms':dict(zip(ROLES,[len(p[3]) for p in role])),
        'ordinary_boundary_e3_terms':{label:len(p) for label,p in eqs},
        'exported_terms':{label:len(p) for label,p in reduced},
        'total_exported_terms':sum(len(p) for _,p in reduced),
        'exported_degree_histograms':{label:{str(d):n for d,n in sorted(Counter(sum(e for _,e in unpack(t)) for t in p).items())} for label,p in reduced},
        'difference_certificates':certificates,'top_path_identity_verified':True,
        'role_e2_equals_unary_quadratic_power_moment_verified':True,
        'existing_reduced_moment_generators_degree_at_most3':len(low),
        'existing_low_degree_polynomial_span_rank':before,
        'augmented_low_degree_polynomial_span_rank':after,
        'rank_scope':'F3 linear span only; excludes variable multiples and higher-degree cancellations',
        'histogram_check':multiplicity_check(),
        'existing_valid_boards_checked':len(fixtures),'full_count_status':'UNEVALUATED; no solver',
    }
    return encoded,audit


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true')
    args=parser.parse_args();encoded,audit=build()
    for name,text in [('exact_f3_math_e3_constraints.json',encoded),
                      ('exact_f3_math_e3_audit.json',json.dumps(audit,indent=2)+'\n')]:
        path=HERE/name
        if args.check:assert path.read_text()==text
        else:path.write_text(text)
    print(json.dumps(audit,indent=2))


if __name__=='__main__':main()
