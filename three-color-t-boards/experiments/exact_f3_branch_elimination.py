#!/usr/bin/env python3
"""Exact affine elimination inside the four sign branches; no solver."""
from pathlib import Path
from itertools import product
from collections import Counter
import argparse,hashlib,json,random
import exact_f3_math as native
import exact_f3_math_e3 as cubic
import exact_f3_order as ordering
import exact_f3_sign_branches as branches

HERE=Path(__file__).resolve().parent


def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(obj):return json.dumps(obj,indent=2)+'\n'
def packed_affine(constant,linear):
    out={1<<(4*v):c for v,c in linear.items()}
    if constant:out[0]=constant
    return out

def coefficient_affine(poly):
    constant=poly.get(0,0);linear={}
    for t,c in poly.items():
        if not t:continue
        pairs=native.unpack(t);assert len(pairs)==1 and pairs[0][1]==1
        linear[pairs[0][0]]=c
    return constant,linear


def solve(k,pivots,delta):
    rows=[r.copy() for r in delta[:k+1]];rhs=[int(i==k) for i in range(k+1)]
    for i,pivot in enumerate(pivots):
        j=next(j for j in range(i,k+1) if rows[j].get(pivot,0))
        rows[i],rows[j]=rows[j],rows[i];rhs[i],rhs[j]=rhs[j],rhs[i]
        inv=rows[i][pivot];rows[i]={v:c*inv%3 for v,c in rows[i].items()};rhs[i]=rhs[i]*inv%3
        for j in range(k+1):
            if j!=i and rows[j].get(pivot,0):
                factor=rows[j][pivot];native.add_into(rows[j],rows[i],-factor)
                rhs[j]=(rhs[j]-factor*rhs[i])%3
    substitutions={}
    for pivot,row,b in zip(pivots,rows,rhs):
        assert row[pivot]==1
        linear={v:-c%3 for v,c in row.items() if v!=pivot}
        assert not set(linear)&set(pivots)
        substitutions[pivot]=packed_affine(b,linear)
    return substitutions


def reducer(substitutions):
    pivots=sorted(substitutions);mask=sum(15<<(4*p) for p in pivots)
    powers={p:[{0:1},f,native.multiply(f,f)] for p,f in substitutions.items()}
    products={0:{0:1}}
    def multiply_pattern(pattern):
        if pattern in products:return products[pattern]
        out={0:1}
        for p in pivots:
            e=pattern>>(4*p)&15
            assert e<=2
            if e:out=native.multiply(out,powers[p][e])
        products[pattern]=out
        return out
    def reduce(poly):
        out={}
        for word,c in poly.items():
            pattern=word&mask;rest=word^pattern
            for term,d in multiply_pattern(pattern).items():
                key=native.field_reduce(rest+term)
                value=(out.get(key,0)+c*d)%3
                if value:out[key]=value
                elif key in out:del out[key]
        return out
    return reduce


def candidates(k):
    if k==0:return [(0,)]
    if k==1:return [(0,a) for a in (15,70,71,93)]
    if k==2:return [(0,a,b) for a in (15,70,71,93) for b in (7,8,9)]
    return [(0,a,b,1) for a in (15,70,71,93) for b in (7,8,9)]


def select_pivots(k,delta,coupled):
    scores=[];best=None
    for pivots in candidates(k):
        subs=solve(k,pivots,delta);reduce=reducer(subs)
        changed=[reduce(p) for p in coupled]
        key=(sum(map(len,changed)),max(map(len,changed)),pivots)
        scores.append({'pivots':list(pivots),'total_coupled_terms':key[0],
                       'largest_coupled_polynomial_terms':key[1],
                       'moment_terms':sum(map(len,changed[:76])),
                       'e3_terms':sum(map(len,changed[76:]))})
        if best is None or key<best[0]:best=(key,subs,changed)
    return best,scores


def remap(poly,mapping):return {ordering.remap_word(t,mapping):c for t,c in poly.items()}

def canonical_digest(poly):return sha(dump(native.polynomial_record('',poly)).encode())

def normalize(poly):
    out={}
    for t,c in poly.items():native.add_into(out,{native.field_reduce(t):c})
    return out

def affine_substitute(poly,substitutions):
    # Only affine inputs: exact ordinary identity, with no field reduction.
    out={}
    for t,c in poly.items():
        if not t:native.add_into(out,{0:c});continue
        pair=native.unpack(t);assert len(pair)==1 and pair[0][1]==1
        v=pair[0][0];native.add_into(out,substitutions.get(v,{t:1}),c)
    return out

def fresh_moments(windows,cell_affines):
    powers={c:[{0:1},p,native.multiply(p,p)] for c,p in cell_affines.items()}
    result={}
    for e in product(range(3),repeat=4):
        if not any(e):continue
        out={0:2} if e==(2,2,2,2) else {}
        for window in windows:
            q={0:1}
            for c,power in zip(window,e):
                if power:q=native.multiply(q,powers[c][power])
            native.add_into(out,q)
        result[e]=out
    return result

def fresh_e3(roles,order,cell_affines):
    def elementary(cells):return cubic.elementary([cell_affines[c] for c in order if c in cells])[3]
    result=[normalize(elementary(roles[0]))]
    for a,b in ((0,2),(2,1),(2,3)):
        p=elementary(roles[a]-roles[b]);native.add_into(p,elementary(roles[b]-roles[a]),-1)
        result.append(normalize(p))
    return result

def parse(text,n):
    import re
    head,prime,body=text.split('\n',2)
    assert head==','.join(f'x{i+1}' for i in range(n)) and prime=='3'
    out=[]
    for expression in body.strip().split(',\n'):
        poly={}
        for summand in expression.split('+'):
            c=1;word=0
            for factor in summand.split('*'):
                if factor in ('1','2'):c=c*int(factor)%3
                else:
                    match=re.fullmatch(r'x([1-9][0-9]*)(?:\^([1-9][0-9]*))?',factor)
                    assert match
                    v=int(match[1])-1;e=int(match[2] or '1')
                    assert 0<=v<n and 0<e<16 and not(word>>(4*v)&15)
                    word+=e<<(4*v)
            native.add_into(poly,{word:c})
        out.append(poly)
    return out

def linear_domain_certificate(p):
    cube=cubic.ordinary_multiply(cubic.ordinary_multiply(p,p),p)
    native.add_into(cube,p,-1)
    constant,linear=coefficient_affine(p);expected={}
    assert (constant**3-constant)%3==0
    for v,c in linear.items():native.add_into(expected,{3<<(4*v):c,1<<(4*v):-c})
    assert cube==expected
    return {'constant':constant,'linear_domain_combination':linear,
            'coefficient_index_space':'old97 natural source variable indices',
            'ordinary_identity':'L^3-L = sum_v coefficient[v]*(x_v^3-x_v)',
            'identity_checked_without_field_reduction':True}

def build():
    manifest_raw=(HERE/'exact_f3_sign_branches_manifest.json').read_bytes()
    assert sha(manifest_raw)=='9ecb49f828699a3966c0349bddb4bc4f57cc163b65ba1855770357bf2e39d2c7'
    manifest=json.loads(manifest_raw)
    original_model_raw=(HERE/'exact_f3_translation_model.json').read_bytes()
    assert sha(original_model_raw)==branches.MODEL_SHA
    original_model=json.loads(original_model_raw)
    old_order_raw=(HERE/'exact_f3_order_selected.json').read_bytes()
    assert sha(old_order_raw)==branches.ORDER_SHA
    old_order=json.loads(old_order_raw)
    windows,roles,gray_order=native.geometry()
    original_forms={int(c):{int(v):a for v,a in f.items()} for c,f in original_model['normalized_color_linear_forms'].items()}
    original_affines={c:packed_affine(0,f) for c,f in original_forms.items()}
    fixtures=json.loads((HERE/'exact_structure_gauge_certificate.json').read_text())['boards']
    files={};branch_records=[];audits=[]
    for branch in manifest['branches']:
        k=branch['branch_id'];natural_path=HERE/branch['natural_input'];minfill_path=HERE/branch['minfill_input']
        raw=natural_path.read_bytes();raw_minfill=minfill_path.read_bytes()
        assert sha(raw)==branch['natural_sha256'] and sha(raw_minfill)==branch['minfill_sha256']
        source=branches.parse97(raw.decode());source_minfill=branches.parse97(raw_minfill.decode())
        source_meta=json.loads(natural_path.with_suffix('.json').read_text())
        delta=[{int(v):c for v,c in r.items()} for r in source_meta['branch_delta_linear_forms']]
        source_to_minfill=old_order['old_index_to_new_index']+[96]
        assert [remap(p,source_to_minfill) for p in source]==source_minfill
        assert len(source)==179+k and len(source[96:176])==80
        # Exhaustively enumerate every coordinate pivot basis of these rows.
        from itertools import combinations
        union=sorted(set().union(*delta[:k+1]));all_bases=[]
        for ps in combinations(union,k+1):
            if native.field_rank([[row.get(v,0) for v in ps] for row in delta[:k+1]])==k+1:all_bases.append(frozenset(ps))
        assert set(all_bases)=={frozenset(ps) for ps in candidates(k)}
        best,scores=select_pivots(k,delta,source[96:176])
        key,subs,changed=best;pivots=list(key[2]);reduce=reducer(subs)
        assert all(0<=v<95 for v in pivots)
        # Every branch equation vanishes as an ordinary affine identity.
        assert all(not affine_substitute(p,subs) for p in source[178:])
        domain_certificates={str(p):linear_domain_certificate(f) for p,f in subs.items()}
        cell_affines={c:affine_substitute(p,subs) for c,p in original_affines.items()}
        assert cell_affines[0]=={}
        fresh=fresh_moments(windows,cell_affines)
        source_exponents=[tuple(e['original_role_exponents']) for e in original_model['moment_equations']]
        assert len(source_exponents)==76
        assert all(fresh[e]==p for e,p in zip(source_exponents,changed[:76]))
        assert all(not p for e,p in fresh.items() if e not in set(source_exponents))
        assert fresh_e3(roles,gray_order,cell_affines)==changed[76:]
        assert all(changed) # every one of the 76 moments and four e3 survives
        remaining=[i for i in range(97) if i not in pivots]
        minfill_remaining=[i for i in old_order['new_index_to_old_index']+[96] if i not in pivots]
        n=len(remaining);assert n==96-k and remaining[-2:]==minfill_remaining[-2:]==[95,96]
        # Every original prefix variable is reconstructed affinely; surviving
        # variables reconstruct identically and inverse projection is literal.
        all_old_affines={i:subs.get(i,{1<<(4*i):1}) for i in range(97)}
        assert all(not(set(v for t in p for v,e in native.unpack(t))&set(pivots)) for p in all_old_affines.values())
        rng=random.Random(0xaff300+k)
        for _ in range(8):
            point=[rng.randrange(3) for _ in range(97)]
            expanded=point.copy()
            for p,f in subs.items():expanded[p]=native.evaluate(f,point)
            assert all(native.evaluate(p,expanded)==0 for p in source[178:])
            for old in remaining:assert expanded[old]==point[old]
            cells={c:native.evaluate(p,point) for c,p in cell_affines.items()}
            assert cells[0]==0
            diff=branches.delta(cells,windows)
            assert diff[:k]==[0]*k and diff[k]==1
            cumulative=[];acc=0
            for c in gray_order:acc=(acc+cells[c])%3;cumulative.append(acc)
            assert [cumulative[j] for j in original_model['free_normalized_prefix_variables']]==expanded[:95]
        checks=0;full_checks=0
        for entry in fixtures:
            z=list(map(int,entry['flat']));diff=branches.delta(z,windows)
            if branches.first_nonzero(diff)!=k:continue
            assert len({tuple(z[c] for c in w) for w in windows})==81
            a=z[0];s=diff[k];d=[s*(c-a)%3 for c in z]
            cumulative=[];acc=0
            for c in gray_order:acc=(acc+d[c])%3;cumulative.append(acc)
            point=[cumulative[j] for j in original_model['free_normalized_prefix_variables']]+[a,s]
            assert all(native.evaluate(f,point)==point[p] for p,f in subs.items())
            assert all(native.evaluate(f,point)==d[c] for c,f in cell_affines.items())
            assert all((a+s*native.evaluate(f,point))%3==z[c] for c,f in cell_affines.items())
            if full_checks<2:
                assert all(native.evaluate(p,point)==0 for p in changed);full_checks+=1
            checks+=1
        variant_records=[];variant_polys={}
        for variant,free_old in (('natural',remaining),('minfill',minfill_remaining)):
            mapping={old:new for new,old in enumerate(free_old)}
            aindex=mapping[95];sindex=mapping[96];assert (aindex,sindex)==(n-2,n-1)
            moved_subs={str(p):remap(f,mapping) for p,f in subs.items()}
            moved_all={str(i):remap(f,mapping) for i,f in all_old_affines.items()}
            moved_cells={str(c):remap(f,mapping) for c,f in cell_affines.items()}
            actual={}
            for c,f in moved_cells.items():
                p={1<<(4*aindex):1}
                for t,coefficient in f.items():native.add_into(p,{t+(1<<(4*sindex)):coefficient})
                actual[c]=p
            assert actual['0']=={1<<(4*aindex):1}
            domains=[{3<<(4*i):1,1<<(4*i):2} for i in range(n)]
            moments=[remap(p,mapping) for p in changed[:76]]
            e3=[remap(p,mapping) for p in changed[76:]]
            sign={2<<(4*sindex):1,0:2}
            polynomials=domains+moments+e3+[sign]
            assert len(polynomials)==n+81==177-k
            assert all(not t>>(4*aindex) for p in moments+e3 for t in p)
            text=','.join(f'x{i+1}' for i in range(n))+'\n3\n'+',\n'.join(native.expression(p) for p in polynomials)+'\n'
            assert parse(text,n)==polynomials
            variant_polys[variant]=polynomials
            # Source-by-source reduction certificate, with explicit ordinary
            # domain identities for eliminated coordinates and exact image hashes.
            relations=[]
            for i in range(96):
                if i in pivots:
                    relations.append({'source_generator_index':i,'kind':'eliminated-field-domain',
                                      'affine_domain_identity':domain_certificates[str(i)]})
                else:
                    relations.append({'source_generator_index':i,'kind':'retained-field-domain','new_generator_index':mapping[i]})
            for old_index,p in enumerate(changed,96):
                new_index=n+old_index-96
                assert polynomials[new_index]==remap(p,mapping)
                relations.append({'source_generator_index':old_index,'kind':'affine-substitution-then-field-reduction',
                                  'new_generator_index':new_index,'image_sha256':canonical_digest(polynomials[new_index])})
            relations.append({'source_generator_index':176,'kind':'retained-field-domain','new_generator_index':sindex})
            relations.append({'source_generator_index':177,'kind':'unchanged-sign-square','new_generator_index':len(polynomials)-1})
            for i in range(178,len(source)):relations.append({'source_generator_index':i,'kind':'zero-ordinary-affine-identity'})
            assert sorted(r['source_generator_index'] for r in relations)==list(range(len(source)))
            affine_records={c:{'constant':coefficient_affine(f)[0],
                                'linear':coefficient_affine(f)[1],
                                'polynomial':native.polynomial_record('canonical-color:'+c,f)} for c,f in moved_cells.items()}
            stem=f'exact_f3_branch_elimination_k{k}_{variant}'
            metadata={
              'format':'t-board-f3-affine-linear-branch-elimination-v1','branch_id':k,
              'scope':source_meta['scope'],'coefficient_characteristic':3,'coefficient_field':'F3',
              'ring_type':'ordinary polynomial ring','variables':n,'coupled_variables':n-2,
              'generators':len(polynomials),'individual_field_domain_count':n,
              'moment_count':76,'e3_count':4,'extra_sign_square_count':1,
              'independent_offset_index':aindex,'independent_sign_index':sindex,
              'sign_field_domain_explicit':True,'count_divisor':1,'count_multiplier':1,
              'branch_count_status':'UNEVALUATED; no solver','full_count_rule':'N=N0+N1+N2+N3, exactly one completed count per branch',
              'prefix':'','fixed_original_cells':[],
              'branch_original_condition':source_meta['branch_original_condition'],
              'branch_canonical_condition':source_meta['branch_canonical_condition'],
              'canonical_branch_constraints_eliminated':True,
              'placement_indices':[0,3],'placement_cells':source_meta['placement_cells'],
              'role_order':['T','L','M','R'],
              'source_natural_input':natural_path.name,'source_natural_sha256':sha(raw),
              'source_minfill_input':minfill_path.name,'source_minfill_sha256':sha(raw_minfill),
              'source_generator_index_convention':'zero-based index in the natural97-variable source input',
              'selected_pivots_in_old97_indices':pivots,
              'pivot_search_scope':'every independent coordinate pivot set for the k+1 branch equations; minimize total moment+e3 terms, then largest support, then pivot tuple',
              'pivot_candidates_tested':len(scores),
              'free_variable_order':variant,'new_index_to_old97_index':free_old,
              'old97_to_new_index_for_surviving_variables':mapping,
              'eliminated_old97_affine_polynomials_in_new_variables':{i:native.polynomial_record('old-variable:'+i,f) for i,f in moved_subs.items()},
              'all_old97_affine_polynomials_in_new_variables':{i:native.polynomial_record('old-variable:'+i,f) for i,f in moved_all.items()},
              'canonical_color_affine_forms':affine_records,
              'original_color_degree_at_most2_polynomials':{c:native.polynomial_record('original-color:'+c,p) for c,p in actual.items()},
              'original_color_reconstruction':'z_cell=a+s*d_cell; d_cell is the exported affine polynomial, so reconstruction can contain a term proportional to s',
              'inverse_reconstruction':f'a=z_apex; D=z-a; s=Delta_{k}(D); d=s*D; compute original Gray prefixes; retain exported surviving coordinates and a,s',
              'original_cell_order':gray_order,
              'old95_canonical_prefix_indices':original_model['free_normalized_prefix_variables'],
              'source_generator_image_certificates':relations,
              'affine_field_identity':'(c+sum a_i*y_i)^3-(c+sum a_i*y_i)=sum a_i*(y_i^3-y_i) over F3',
              'moment_and_e3_source_substitution_matches_fresh_geometry':True,
              'reduction_semantics':'ordinary polynomial substitution followed by reduction only modulo surviving y_i^3-y_i domains; zero is an allowed coordinate',
              'monomial_encoding':'[coefficient,hex integer]; ordinary exponent of variable i occupies bits4i..4i+3',
              'input_file':stem+'.ms','input_sha256':sha(text.encode()),
              'generator_counts_before_after':[len(source),len(polynomials)],
              'moment_terms':sum(map(len,moments)),'e3_terms':sum(map(len,e3)),
              'all_polynomial_terms':sum(map(len,polynomials)),
              'largest_polynomial_terms':max(map(len,polynomials)),
              'exact_total_claimed':False,
            }
            files[stem+'.ms']=text;files[stem+'.json']=dump(metadata)
            variant_records.append({'order':variant,'input':stem+'.ms','input_sha256':sha(text.encode()),
                                    'metadata':stem+'.json','metadata_sha256':sha(files[stem+'.json'].encode())})
        natural_to_minfill=[minfill_remaining.index(old) for old in remaining]
        inverse=[remaining.index(old) for old in minfill_remaining]
        # Field generators are emitted in ascending variable order in both
        # rings; renaming therefore permutes that first n-generator block.
        for i,p in enumerate(variant_polys['natural']):
            target=natural_to_minfill[i] if i<n else i
            assert remap(p,natural_to_minfill)==variant_polys['minfill'][target]
        for i,p in enumerate(variant_polys['minfill']):
            target=inverse[i] if i<n else i
            assert remap(p,inverse)==variant_polys['natural'][target]
        branch_records.append({'branch_id':k,'variables':n,'coupled_variables':n-2,'generators':n+81,
                               'selected_old97_pivots':pivots,'moment_terms':sum(map(len,changed[:76])),
                               'e3_terms':sum(map(len,changed[76:])),
                               'representations':variant_records,'count_status':'UNEVALUATED'})
        audits.append({'branch_id':k,'all_independent_coordinate_pivot_sets_tested':len(all_bases),
          'candidate_term_counts':scores,'selected_pivots':pivots,
          'affine_substitutions_in_old97_variables':{str(p):native.expression(f) for p,f in subs.items()},
          'ordinary_affine_constraint_identities_checked':True,
          'ordinary_affine_field_domain_identities_checked':True,
          'all80_fresh_geometric_moments_match_source_images':True,
          'all4_fresh_e3_equations_match_source_images':True,
          'all_source_generators_have_complete_image_certificates':True,
          'all_retained_field_domains_explicit':True,'offset_and_sign_never_eliminated':True,
          'natural_minfill_complete_polynomial_inverse_renaming_checked':True,
          'natural_to_minfill_variable_permutation':natural_to_minfill,
          'natural_to_minfill_generator_permutation':natural_to_minfill+list(range(n,n+81)),
          'arbitrary_free_assignments_roundtripped':8,'existing_valid_boards_roundtripped':checks,
          'complete_transformed_coupled_polynomial_fixture_checks':full_checks,
          'canonical_apex_still_zero':True})
    reduced_manifest={
      'format':'t-board-four-affinely-eliminated-linear-sign-branches-v1',
      'required_branch_ids':[0,1,2,3],'branches':branch_records,
      'scope':'all full labeled valid boards partitioned by first nonzero coordinate of P0-P3',
      'source_manifest':'exact_f3_sign_branches_manifest.json','source_manifest_sha256':sha(manifest_raw),
      'count_rule':'N=N0+N1+N2+N3, one complete certified dimension for each branch',
      'count_multiplier':1,'count_divisor':1,
      'completion_rule':'All four branches must complete. Natural/minfill and reduced/unreduced variants represent the same branch; never add alternative representations. Incomplete results are unknown, not zero.',
      'known_six_prefix_prediction':manifest['known_six_prefix_prediction'],
      'full_count_status':'UNEVALUATED; no solver'}
    files['exact_f3_branch_elimination_manifest.json']=dump(reduced_manifest)
    audit={'status':'PASS','scope':'complete exact affine branch elimination and polynomial exports; no solver',
           'source_manifest_sha256':sha(manifest_raw),'branches':audits,
           'export_sha256':{name:sha(text.encode()) for name,text in files.items()},
           'generator_sha256':sha(Path(__file__).read_bytes()),'full_count_status':'UNEVALUATED'}
    files['exact_f3_branch_elimination_audit.json']=dump(audit)
    return files,audit


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    files,audit=build()
    for name,text in files.items():
        path=HERE/name
        if args.check:assert path.read_text()==text,name
        else:path.write_text(text)
    print(dump({'status':audit['status'],'branches':[{'id':a['branch_id'],'pivots':a['selected_pivots'],
                         'witnesses':a['existing_valid_boards_roundtripped']} for a in audit['branches']],
                'export_sha256':audit['export_sha256']}))
if __name__=='__main__':main()
