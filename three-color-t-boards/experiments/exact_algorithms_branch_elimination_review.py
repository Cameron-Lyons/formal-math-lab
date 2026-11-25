#!/usr/bin/env python3
"""Independent affine elimination audit using ordinary tuple monomials.

No exporter imports and no solver calls. Only explicit surviving F3 domains
justify exponent reduction; constants in eliminated coordinates are retained.
"""
from pathlib import Path
from functools import lru_cache
import hashlib,json,re,random
from exact_algorithms_sign_review import add,mul,linear,packed,val,rename

HERE=Path(__file__).resolve().parent
MANIFEST_SHA='91e25ac8803be65a12998e344060e3e48778e499722f30aaf7b5a663f8b2eaa0'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def accumulate(out,m,c):
    value=(out.get(m,0)+c)%3
    if value:out[m]=value
    else:out.pop(m,None)


def parse(text):
    header,p,body=text.split('\n',2);n=len(header.split(','))
    assert header==','.join(f'x{i+1}' for i in range(n)) and p=='3'
    result=[]
    for expression in body.strip().split(','):
        out={}
        for term in expression.replace('\n','').split('+'):
            c=1;exps={}
            for factor in term.split('*'):
                if factor.isdigit():c=c*int(factor)%3
                else:
                    match=re.fullmatch(r'x([1-9][0-9]*)(?:\^([1-9][0-9]*))?',factor)
                    assert match,factor
                    v=int(match[1])-1;e=int(match[2] or 1)
                    assert v<n and v not in exps;exps[v]=e
            accumulate(out,tuple(sorted(exps.items())),c)
        result.append(out)
    return n,result


def affine_solution(equations,pivots):
    rows=[]
    for p in equations:
        row=[0]*98
        for m,c in p.items():
            if not m:row[97]=-c%3
            else:
                assert len(m)==1 and m[0][1]==1;row[m[0][0]]=c
        rows.append(row)
    assert len(rows)==len(pivots)
    for i,pivot in enumerate(pivots):
        found=next(j for j in range(i,len(rows)) if rows[j][pivot])
        rows[i],rows[found]=rows[found],rows[i]
        inv=pow(rows[i][pivot],-1,3);rows[i]=[c*inv%3 for c in rows[i]]
        for j in range(len(rows)):
            if j!=i:
                c=rows[j][pivot]
                rows[j]=[(a-c*b)%3 for a,b in zip(rows[j],rows[i])]
    substitutions={}
    for pivot,row in zip(pivots,rows):
        assert row[pivot]==1 and all(row[q]==int(q==pivot) for q in pivots)
        p={((v,1),):-c%3 for v,c in enumerate(row[:97]) if c and v!=pivot}
        if row[97]:p[()]=row[97]
        substitutions[pivot]=p
    return substitutions


def substitute_affine(p,substitutions):
    out={}
    for m,c in p.items():
        if not m:accumulate(out,(),c)
        else:
            assert len(m)==1 and m[0][1]==1
            for term,d in substitutions.get(m[0][0],{m:1}).items():accumulate(out,term,c*d)
    return out


def normalized_substituter(substitutions):
    pivots=set(substitutions)
    @lru_cache(None)
    def product(pattern):
        p={():1}
        for v,e in pattern:
            for _ in range(e):p=mul(p,substitutions[v],reduce=True)
        return p
    def substitute(p):
        out={}
        for m,c in p.items():
            pattern=tuple((v,e) for v,e in m if v in pivots)
            rest=dict((v,e) for v,e in m if v not in pivots)
            for term,d in product(pattern).items():
                e=rest.copy()
                for v,k in term:e[v]=e.get(v,0)+k
                reduced=tuple(sorted((v,1+(k-1)%2) for v,k in e.items() if k))
                accumulate(out,reduced,c*d)
        return out
    return substitute


def canonical_hash(p):
    words={sum(e<<(4*v) for v,e in m):c for m,c in p.items()}
    record=dict(label='',terms=[[words[t],hex(t)] for t in sorted(words)])
    return hashlib.sha256((json.dumps(record,indent=2)+'\n').encode()).hexdigest()


def main():
    manifest_path=HERE/'exact_f3_branch_elimination_manifest.json'
    assert sha(manifest_path)==MANIFEST_SHA
    manifest=json.loads(manifest_path.read_text())
    assert manifest['required_branch_ids']==[0,1,2,3]
    assert manifest['count_divisor']==manifest['count_multiplier']==1
    translation=json.loads((HERE/'exact_f3_translation_model.json').read_text())
    source_forms={int(c):linear(f) for c,f in translation['normalized_color_linear_forms'].items()}
    order=json.loads((HERE/'exact_f3_order_selected.json').read_text())
    witnesses=json.loads((HERE/'exact_structure_gauge_certificate.json').read_text())['boards']
    reports=[];old_domains=0;source_images=0;colors_checked=0;roundtrips=0
    for entry in manifest['branches']:
        k=entry['branch_id'];pivots=entry['selected_old97_pivots'];n=96-k
        assert pivots==[[0],[0,71],[0,71,8],[0,71,8,1]][k]
        source_path=HERE/f'exact_f3_sign_branch{k}_natural.ms'
        _,source=parse(source_path.read_text());assert len(source)==179+k
        subs=affine_solution(source[178:],pivots)
        assert all(not substitute_affine(p,subs) for p in source[178:])
        all_affine={i:subs.get(i,{((i,1),):1}) for i in range(97)}
        surviving=[i for i in range(97) if i not in pivots]
        assert all(not(set(v for m in p for v,e in m)&set(pivots)) for p in all_affine.values())
        reduce=normalized_substituter(subs)
        changed=[reduce(p) for p in source[96:176]]
        assert all(changed) and len(changed)==80
        canonical_cells={c:substitute_affine(p,subs) for c,p in source_forms.items()}
        assert canonical_cells[0]=={}
        # Ordinary characteristic-three identities, before any field reduction.
        for old,p in all_affine.items():
            cube_minus=add(mul(mul(p,p),p),p,-1);expected={}
            for m,c in p.items():
                if m:
                    assert len(m)==1 and m[0][1]==1
                    v=m[0][0];expected=add(expected,{((v,3),):c,((v,1),):-c%3})
                else:assert (c**3-c)%3==0
            assert cube_minus==expected;old_domains+=1
        variants=[]
        for rep in entry['representations']:
            label=rep['order'];path=HERE/rep['input'];meta_path=HERE/rep['metadata']
            assert sha(path)==rep['input_sha256'] and sha(meta_path)==rep['metadata_sha256']
            meta=json.loads(meta_path.read_text());actual_n,actual=parse(path.read_text())
            assert actual_n==n and len(actual)==177-k
            free=(surviving if label=='natural' else
                  [i for i in order['new_index_to_old_index']+[96] if i not in pivots])
            mapping={old:new for new,old in enumerate(free)}
            assert free==meta['new_index_to_old97_index'] and free[-2:]==[95,96]
            assert {str(old):new for old,new in mapping.items()}==meta['old97_to_new_index_for_surviving_variables']
            assert meta['independent_offset_index']==n-2 and meta['independent_sign_index']==n-1
            assert meta['selected_pivots_in_old97_indices']==pivots
            assert sha(source_path)==meta['source_natural_sha256']
            assert sha(HERE/meta['source_minfill_input'])==meta['source_minfill_sha256']
            for old,p in all_affine.items():
                renamed=rename(p,mapping)
                assert packed(meta['all_old97_affine_polynomials_in_new_variables'][str(old)])==renamed
                if old in subs:
                    assert packed(meta['eliminated_old97_affine_polynomials_in_new_variables'][str(old)])==renamed
                else:assert renamed=={((mapping[old],1),):1}
            expected=[{((i,3),):1,((i,1),):2} for i in range(n)]
            expected += [rename(p,mapping) for p in changed]
            expected += [{((n-1,2),):1,():2}]
            assert actual==expected
            assert all(e<=2 for p in actual[n:] for m in p for v,e in m)
            assert all(v<n-2 for p in actual[n:n+80] for m in p for v,e in m)
            assert meta['variables']==meta['individual_field_domain_count']==n
            assert meta['generators']==n+81 and meta['coupled_variables']==n-2
            assert meta['count_divisor']==meta['count_multiplier']==1
            assert not meta['prefix'] and meta['fixed_original_cells']==[] and not meta['exact_total_claimed']
            certificates=meta['source_generator_image_certificates']
            assert [c['source_generator_index'] for c in certificates]==list(range(179+k))
            for index,c in enumerate(certificates):
                kind=c['kind']
                if index<96 or index==176:
                    old=index if index<96 else 96
                    if old in pivots:
                        assert kind=='eliminated-field-domain'
                        cert=c['affine_domain_identity'];p=subs[old]
                        assert cert['constant']==p.get((),0)
                        assert cert['linear_domain_combination']=={str(m[0][0]):a for m,a in p.items() if m}
                        assert cert['coefficient_index_space']=='old97 natural source variable indices'
                    else:
                        assert kind=='retained-field-domain' and c['new_generator_index']==mapping[old]
                elif index<176:
                    target=n+index-96
                    assert kind=='affine-substitution-then-field-reduction' and c['new_generator_index']==target
                    assert c['image_sha256']==canonical_hash(expected[target])
                elif index==177:
                    assert kind=='unchanged-sign-square' and c['new_generator_index']==len(actual)-1
                else:assert kind=='zero-ordinary-affine-identity'
                source_images+=1
            constants=0
            for cell,p in canonical_cells.items():
                moved=rename(p,mapping);record=meta['canonical_color_affine_forms'][str(cell)]
                assert packed(record['polynomial'])==moved and record['constant']==moved.get((),0)
                assert record['linear']=={str(m[0][0]):a for m,a in moved.items() if m}
                if record['constant']:constants+=1
                color=add({((n-2,1),):1},mul({((n-1,1),):1},moved))
                assert packed(meta['original_color_degree_at_most2_polynomials'][str(cell)])==color
                colors_checked+=1
            assert constants>0
            rng=random.Random(91000+100*k+(label=='minfill'))
            for _ in range(12):
                point=[rng.randrange(3) for _ in range(n)]
                old=[val(rename(all_affine[i],mapping),point) for i in range(97)]
                assert all(val(p,old)==0 for p in source[178:])
                assert [old[i] for i in free]==point
                cells=[val(rename(canonical_cells[c],mapping),point) for c in range(100)]
                acc=0;prefix=[]
                for cell in meta['original_cell_order']:acc=(acc+cells[cell])%3;prefix.append(acc)
                assert [prefix[i] for i in meta['old95_canonical_prefix_indices']]==old[:95]
            witness_count=0
            for witness in witnesses:
                z=list(map(int,witness['flat']))
                delta=[(z[a]-z[b])%3 for a,b in zip([0,1,2,3],[3,6,7,8])]
                branch=next(i for i,c in enumerate(delta) if c)
                if branch!=k:continue
                a=z[0];s=delta[k];d=[s*(c-a)%3 for c in z];acc=0;prefix=[]
                for cell in meta['original_cell_order']:acc=(acc+d[cell])%3;prefix.append(acc)
                old=[prefix[i] for i in meta['old95_canonical_prefix_indices']]+[a,s]
                point=[old[i] for i in free]
                assert [val(rename(all_affine[i],mapping),point) for i in range(97)]==old
                assert [val(packed(meta['original_color_degree_at_most2_polynomials'][str(c)]),point) for c in range(100)]==z
                witness_count+=1;roundtrips+=1
            variants.append(dict(order=label,variables=n,generators=len(actual),input_sha256=sha(path),
                metadata_sha256=sha(meta_path),all_source_images_checked=True,
                polynomial_terms=sum(map(len,actual)),max_degree=max(sum(e for v,e in m) for p in actual for m in p),
                nonzero_affine_color_constants=constants,witness_roundtrips=witness_count,
                arbitrary_free_assignments_roundtripped=12))
        reports.append(dict(branch=k,pivots=pivots,variants=variants))
        print(f'branch {k}: all polynomial images, domains, coordinate maps and both inputs PASS',flush=True)
    result=dict(status='PASS',scope='independent affine-eliminated branch-model audit; no solver',
        manifest_sha256=MANIFEST_SHA,branches=reports,ordinary_old_variable_domain_identities=old_domains,
        source_generator_certificates=source_images,original_color_forms=colors_checked,
        known_board_roundtrips=roundtrips,count_multiplier=1,count_divisor=1,
        generator_imported=False,solver_runs=0,reviewer_sha256=sha(Path(__file__)))
    (HERE/'exact_algorithms_branch_elimination_review.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
