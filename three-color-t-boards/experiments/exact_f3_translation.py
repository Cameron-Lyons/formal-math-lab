#!/usr/bin/env python3
"""Separate exact native-F3 translation factorization; no solver runs."""
from collections import Counter
from itertools import product
from math import comb
from pathlib import Path
import argparse
import hashlib
import json
import random

import exact_f3_math as native
import exact_f3_math_e3 as cubic

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'exact_f3_math_model.json'
SOURCE_SHA256='fe1321842be3bf5bdb8ff91cd5b9c38017d542968fe27a8d5a8952e344564cc4'
E3_SOURCE=HERE/'exact_f3_math_e3_constraints.json'
E3_SOURCE_SHA256='6cef0fb4e6b3ccb80f17f7aebadfd02fd777d082e1dedb84cdf5d9786d408392'
OFFSET_INDEX=95


def parse_poly(record):return {int(t,16):c for c,t in record['terms']}


def identify_prefix(poly,old_free,new_free):
    indices={p:i for i,p in enumerate(new_free)}
    out={}
    for term,c in poly.items():
        word=0
        for variable,power in native.unpack(term):
            prefix=old_free[variable]
            if prefix==8:prefix=7
            word+=power<<(4*indices[prefix])
        native.add_into(out,{native.field_reduce(word):c})
    return out


def degree(poly):return max((sum(e for _,e in native.unpack(t)) for t in poly),default=-1)


def linear_field_identity(forms):
    # Ordinary-ring check; no field reduction makes either side zero here.
    for linear in forms.values():
        p={1<<(4*v):c for v,c in linear.items()}
        cube=cubic.ordinary_multiply(cubic.ordinary_multiply(p,p),p)
        native.add_into(cube,p,-1)
        expected={}
        for v,c in linear.items():native.add_into(expected,{3<<(4*v):c,1<<(4*v):-c})
        assert cube==expected


def build():
    raw=SOURCE.read_bytes();assert hashlib.sha256(raw).hexdigest()==SOURCE_SHA256
    old=json.loads(raw)
    raw_e3=E3_SOURCE.read_bytes();assert hashlib.sha256(raw_e3).hexdigest()==E3_SOURCE_SHA256
    old_e3=json.loads(raw_e3)
    windows,roles,order=native.geometry()
    _,old_subs,old_free,old_forms=native.coordinates(roles,order)
    new_free=[p for p in old_free if p!=8];index={p:i for i,p in enumerate(new_free)}
    assert len(new_free)==95 and old_free==old['free_prefix_variables']
    normalized_forms={}
    for cell,linear in old_forms.items():
        p={}
        for variable,c in linear.items():
            prefix=old_free[variable]
            if prefix==8:prefix=7
            native.add_into(p,{index[prefix]:c})
        normalized_forms[cell]=p
    assert normalized_forms[0]=={}
    original_forms={cell:linear.copy() for cell,linear in normalized_forms.items()}
    for linear in original_forms.values():linear[OFFSET_INDEX]=1
    assert original_forms[0]=={OFFSET_INDEX:1}
    linear_field_identity(original_forms)

    # Complete symbolic prefix reconstruction; original prefix j shifts by
    # (j+1)*a, while normalized prefix8 equals prefix7.
    normalized_prefix={}
    for p in range(100):
        linear=old_subs.get(p,{p:1});out={}
        for q,c in linear.items():
            if q==8:q=7
            native.add_into(out,{index[q]:c})
        normalized_prefix[p]=out
    accumulated={}
    for position,cell in enumerate(order):
        native.add_into(accumulated,original_forms[cell])
        expected=normalized_prefix[position].copy()
        native.add_into(expected,{OFFSET_INDEX:(position+1)%3})
        assert accumulated==expected

    moments,eliminated=native.moment_polynomials(windows,normalized_forms)
    old_moments={tuple(e['original_role_exponents']):parse_poly(e) for e in old['moment_equations']}
    normalized_moments={e:p for e,_,p in moments}
    assert set(old_moments)==set(normalized_moments)
    for e,p in old_moments.items():
        assert identify_prefix(p,old_free,new_free)==normalized_moments[e]

    # Direct fresh moments of a+d match the full binomial triangular transform
    # of the normalized zero-polynomials, including the nonzero maximal target.
    translated,translated_zero=native.moment_polynomials(windows,original_forms)
    assert translated_zero==eliminated
    for e,_,direct in translated:
        expected={}
        for f in product(*(range(power+1) for power in e)):
            if not any(f):continue # M0000=81=0
            coefficient=1
            for upper,lower in zip(e,f):coefficient=coefficient*comb(upper,lower)%3
            if not coefficient:continue
            offset_power=sum(e)-sum(f)
            extra=(0 if offset_power==0 else (1+(offset_power-1)%2)<<(4*OFFSET_INDEX))
            for term,c in normalized_moments.get(f,{}).items():
                native.add_into(expected,{term+extra:coefficient*c})
        assert expected==direct
    assert all(not t>>(4*OFFSET_INDEX) for _,_,p in moments for t in p)

    # Fresh normalized elementary cubics, compared to substitution in the
    # separately frozen native augmentation.
    linears={cell:{1<<(4*v):c for v,c in linear.items()} for cell,linear in normalized_forms.items()}
    def sym(cells):return cubic.elementary([linears[c] for c in order if c in cells])
    role=[sym(cells) for cells in roles]
    e3=[('e3:T',role[0][3])]
    for a,b in ((0,2),(2,1),(2,3)):
        left,right=sym(roles[a]-roles[b]),sym(roles[b]-roles[a])
        e3.append(('e3:'+('T','L','M','R')[a]+':'+('T','L','M','R')[b],
                   cubic.difference(left[3],right[3])))
    e3=[(label,cubic.normalized(p)) for label,p in e3]
    for saved,(label,p) in zip(old_e3['equations'],e3):
        assert saved['label']==label
        assert identify_prefix(parse_poly(saved),old_free,new_free)==p
    assert all(not t>>(4*OFFSET_INDEX) for _,p in e3 for t in p)

    # Check e3(z+a)=e3(z)+a*e2(z)+a²*e1(z) as an ordinary
    # polynomial identity for all four actual role sets.
    offset={1<<(4*OFFSET_INDEX):1};offset2={2<<(4*OFFSET_INDEX):1}
    translated_linears={cell:{1<<(4*v):c for v,c in f.items()} for cell,f in original_forms.items()}
    for i,cells in enumerate(roles):
        shifted=cubic.elementary([translated_linears[c] for c in order if c in cells])[3]
        expected=role[i][3].copy()
        native.add_into(expected,cubic.ordinary_multiply(offset,role[i][2]))
        native.add_into(expected,cubic.ordinary_multiply(offset2,role[i][1]))
        assert shifted==expected

    rng=random.Random(0x3fac)
    for _ in range(12):
        free_values=[rng.randrange(3) for _ in new_free]
        for a in range(3):
            values=free_values+[a]
            normalized={c:sum(coef*values[v] for v,coef in f.items())%3 for c,f in normalized_forms.items()}
            full={c:(z+a)%3 for c,z in normalized.items()}
            assert full[0]==a
            prefix=[];s=0
            for c in order:s=(s+full[c])%3;prefix.append(s)
            assert [((prefix[p]-(p+1)*a)%3) for p in new_free]==free_values
            for e,target,p in moments:
                direct=0
                for w in windows:
                    value=1
                    for c,power in zip(w,e):value=value*pow(normalized[c],power,3)%3
                    direct=(direct+value)%3
                assert native.evaluate(p,values)==(direct-target)%3
    fixtures=json.loads((HERE/'exact_structure_gauge_certificate.json').read_text())['boards']
    for entry in fixtures:
        z=list(map(int,entry['flat']));a=z[0];d=[(v-a)%3 for v in z]
        prefix=[];s=0
        for c in order:s=(s+d[c])%3;prefix.append(s)
        values=[prefix[p] for p in new_free]+[a]
        assert all(sum(coef*values[v] for v,coef in f.items())%3==z[c] for c,f in original_forms.items())
        assert all(native.evaluate(p,values)==0 for _,_,p in moments)
        assert all(native.evaluate(p,values)==0 for _,p in e3)

    domains=[{3<<(4*i):1,1<<(4*i):2} for i in range(96)]
    common={
        'variables':96,'coefficient_characteristic':3,'coefficient_field':'F3',
        'ring_type':'ordinary polynomial ring','scope':'full labeled ternary boards',
        'extension_variable':False,'original_cell_order':order,
        'free_normalized_prefix_variables':new_free,'offset_variable_index':OFFSET_INDEX,
        'offset_semantics':'a is original apex color; independent F3 parameter, not an extension-field generator',
        'normalized_apex_condition':'d0=0, imposed by u8=u7',
        'original_color_reconstruction':'z_cell=a+d_cell',
        'source_native_model_sha256':SOURCE_SHA256,
        'monomial_encoding':'hex integer: ordinary exponent of variable i in bits4*i..4*i+3',
        'term_encoding':'[coefficient,hex_monomial], coefficient1 or2 modulo3; complete zero polynomial',
        'prefix':'','fixed_original_cells':[],'symmetry_normalization':False,
        'count_divisor':1,'count_multiplier':1,
        'full_count_status':'UNEVALUATED; no solver',
    }
    document=dict(common,format='t-board-natural-f3-translation-v1',
        domain_equations=[native.polynomial_record(f'field:{i}',p) for i,p in enumerate(domains)],
        moment_equations=[dict(native.polynomial_record('moment:'+','.join(map(str,e)),p),
                               original_role_exponents=list(e),target_moment=target,target_already_subtracted=True)
                          for e,target,p in moments],
        normalized_color_linear_forms={str(c):{str(v):a for v,a in sorted(f.items())} for c,f in sorted(normalized_forms.items())},
        original_color_linear_forms={str(c):{str(v):a for v,a in sorted(f.items())} for c,f in sorted(original_forms.items())},
        normalized_prefix_linear_forms={str(p):{str(v):a for v,a in sorted(f.items())} for p,f in normalized_prefix.items()},
        linear_form_indices='compressed normalized-prefix variables0..94; offset95',
        independent_offset_domain='x96^3-x96',coupled_variables=95,
        generators=172,retained_moments=76,extra_histogram_equations=False)
    model_text=json.dumps(document,indent=2)+'\n';model_sha=hashlib.sha256(model_text.encode()).hexdigest()
    e3_document=dict(common,format='t-board-natural-f3-translation-e3-v1',augmentation_only=True,
        source_translation_model_sha256=model_sha,source_native_e3_sha256=E3_SOURCE_SHA256,
        required_base='retain all96 field cubics and76 normalized moments, including unary quadratic moments',
        equations=[native.polynomial_record(label,p) for label,p in e3])
    e3_text=json.dumps(e3_document,indent=2)+'\n'
    def ms(polys):return ','.join(f'x{i+1}' for i in range(96))+'\n3\n'+',\n'.join(native.expression(p) for p in polys)+'\n'
    base_ms=ms(domains+[p for _,_,p in moments])
    augmented_ms=ms(domains+[p for _,_,p in moments]+[p for _,p in e3])
    old_low=[p for p in old_moments.values() if degree(p)<=3]
    new_low=[p for _,_,p in moments if degree(p)<=3]
    audit={
        'status':'PASS','scope':'full-count factorization retained inside96-variable input; no solver',
        'variables':96,'coupled_variables':95,'independent_offset_variables':1,
        'offset_appears_only_in_its_field_domain':True,
        'source_native_model_sha256':SOURCE_SHA256,
        'base_moment_terms':sum(map(len,old_moments.values())),
        'translation_moment_terms':sum(len(p) for _,_,p in moments),
        'translation_moment_degree_histogram':{str(d):n for d,n in sorted(Counter(degree(p) for _,_,p in moments).items())},
        'base_low_degree_count':len(old_low),'translation_low_degree_count':len(new_low),
        'base_low_degree_rank':cubic.rank(old_low),'translation_low_degree_rank':cubic.rank(new_low),
        'translation_low_degree_rank_with_e3':cubic.rank(new_low+[p for _,p in e3]),
        'normalized_e3_term_counts':{label:len(p) for label,p in e3},
        'fresh_normalized_moments_match_apex_identification':True,
        'all80_moment_translation_identities_checked':True,
        'ordinary_field_ideal_transform_checked':True,
        'ordinary_role_e3_shift_identities_checked':True,
        'random_normalized_assignments_checked_at_all3_offsets':12,
        'existing_valid_boards_roundtripped':len(fixtures),
        'count_divisor':1,'count_multiplier':1,
        'full_count_status':'UNEVALUATED',
    }
    files=[('exact_f3_translation_model.json',model_text),('exact_f3_translation_e3_constraints.json',e3_text),
           ('exact_f3_translation_model.ms',base_ms),('exact_f3_translation_e3.ms',augmented_ms)]
    audit['files']=[{'file':name,'sha256':hashlib.sha256(text.encode()).hexdigest()} for name,text in files]
    return files,audit


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true')
    args=parser.parse_args();files,audit=build()
    files.append(('exact_f3_translation_audit.json',json.dumps(audit,indent=2)+'\n'))
    for name,text in files:
        path=HERE/name
        if args.check:assert path.read_text()==text
        else:path.write_text(text)
    print(json.dumps(audit,indent=2))


if __name__=='__main__':main()
