#!/usr/bin/env python3
"""Small finite-field sign-selector research; never launches a solver."""
from itertools import product,combinations,permutations
from pathlib import Path
from collections import Counter
import hashlib,json,argparse
import exact_f3_math as native

HERE=Path(__file__).resolve().parent

def rem(poly,divisor):
    poly=list(poly)
    while poly and poly[-1]==0:poly.pop()
    while len(poly)>=len(divisor):
        c=poly[-1];offset=len(poly)-len(divisor)
        for j,d in enumerate(divisor):poly[offset+j]=(poly[offset+j]-c*d)%3
        while poly and poly[-1]==0:poly.pop()
    return poly

def irreducibles():
    divisors=[list(c)+[1] for d in (1,2) for c in product(range(3),repeat=d)]
    return [list(c)+[1] for c in product(range(3),repeat=5) if c[0] and all(rem(list(c)+[1],d) for d in divisors)]

class Field:
    def __init__(self,modulus):self.mod=modulus
    def add(self,a,b):return tuple((x+y)%3 for x,y in zip(a,b))
    def mul(self,a,b):
        c=[0]*9
        for i,x in enumerate(a):
            for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%3
        for i in range(8,4,-1):
            for j in range(5):c[i-5+j]=(c[i-5+j]-c[i]*self.mod[j])%3
        return tuple(c[:5])
    def power(self,a,n):
        out=(1,0,0,0,0)
        while n:
            if n&1:out=self.mul(out,a)
            a=self.mul(a,a);n//=2
        return out
    def norm_poly(self,basis):
        out={(0,0,0,0):(1,0,0,0,0)}
        for k in range(5):
            terms=[self.power(b,3**k) for b in basis];new={}
            for m,c in out.items():
                for i,b in enumerate(terms):
                    e=list(m);e[i]+=1;e=tuple(e)
                    new[e]=self.add(new.get(e,(0,)*5),self.mul(c,b))
            out={m:c for m,c in new.items() if any(c)}
        assert all(not any(c[1:]) for c in out.values())
        return {m:c[0] for m,c in out.items()}

def reduce_poly(p):
    out={}
    for powers,c in p.items():
        key=tuple(0 if e==0 else 1+(e-1)%2 for e in powers)
        v=(out.get(key,0)+c)%3
        if v:out[key]=v
        elif key in out:del out[key]
    return out

def value(p,x):
    result=0
    for e,c in p.items():
        for a,b in zip(x,e):c=c*pow(a,b,3)%3
        result=(result+c)%3
    return result

def norm_candidates():
    moduli=irreducibles();assert len(moduli)==48
    result=[]
    for modulus in moduli:
        field=Field(modulus)
        for indices in combinations(range(5),4):
            basis=[tuple(int(i==j) for i in range(5)) for j in indices]
            ordinary=field.norm_poly(basis);reduced=reduce_poly(ordinary)
            result.append((len(reduced),len(ordinary),modulus,indices,ordinary,reduced))
    result.sort(key=lambda r:r[:4])
    return result

def expression(p,names=('u','v','w','t')):
    terms=[]
    for powers,c in sorted(p.items(),key=lambda x:(sum(x[0]),x[0])):
        parts=[] if c==1 else ['2']
        parts += [name if e==1 else name+'^'+str(e) for name,e in zip(names,powers) if e]
        terms.append('*'.join(parts) or '1')
    return '+'.join(terms) or '0'

def optimize_norm(candidates):
    best=None;trials=0
    # Fixed deterministic local search, not a global sparsity optimum.
    for start in candidates[:24]:
        field=Field(start[2])
        basis=[tuple(int(i==j) for i in range(5)) for j in start[3]]
        p=field.norm_poly(basis);key=(len(reduce_poly(p)),len(p));moves=[]
        while True:
            proposals=[]
            for i in range(4):
                for j in range(4):
                    if i==j:continue
                    for c in (1,2):
                        b=basis.copy();b[j]=field.add(b[j],tuple(c*x%3 for x in b[i]))
                        q=field.norm_poly(b);k=(len(reduce_poly(q)),len(q));trials+=1
                        proposals.append((k,i,j,c,b,q))
            move=min(proposals,key=lambda x:x[:4])
            if move[0]>=key:break
            key,i,j,c,basis,p=move;moves.append([i,j,c])
        candidate=(key,start[2],start[3],moves,basis,p)
        if best is None or key<best[0]:best=candidate
    return best,trials


def compose(poly,forms):
    powers=[]
    for linear in forms:
        q={1<<(4*v):c for v,c in linear.items()}
        powers.append([{0:1},q,native.multiply(q,q)])
    out={}
    for exponents,c in poly.items():
        q={0:c}
        for i,e in enumerate(exponents):q=native.multiply(q,powers[i][e])
        native.add_into(out,q)
    return out


def sha(data):return hashlib.sha256(data).hexdigest()

def record_tuple(poly):return [[c,list(e)] for e,c in sorted(poly.items())]

def signed_permute(poly,perm,signs):
    out={}
    for exponents,c in poly.items():
        e=[0]*4
        for old,new in enumerate(perm):
            e[new]=exponents[old];c=c*pow(signs[old],exponents[old],3)%3
        out[tuple(e)]=c
    return out


def build():
    import exact_f3_order as ordering
    source=HERE/'exact_f3_translation_e3.ms'
    model_path=HERE/'exact_f3_translation_model.json'
    order_path=HERE/'exact_f3_order_selected.json'
    source_raw=source.read_bytes();model_raw=model_path.read_bytes();order_raw=order_path.read_bytes()
    assert sha(source_raw)=='44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5'
    assert sha(model_raw)=='1e2dc884f8996c6bd1b5093f24fa6fe7d7f1002e97b69762baadfda5adf94a7f'
    assert sha(order_raw)=='387d85417ffb7823ceef2984b506b39f6913169491d7ada2d75343ec1829bc3e'
    model=json.loads(model_raw);order=json.loads(order_raw)
    candidates=norm_candidates();best,search_trials=optimize_norm(candidates)
    cost,modulus,initial_indices,shears,basis,ordinary=best
    reduced=reduce_poly(ordinary)
    assert cost==(17,38)
    field=Field(modulus)
    points=list(product(range(3),repeat=4))
    image=[]
    for point in points:
        element=(0,)*5
        for b,c in zip(basis,point):element=field.add(element,tuple(c*x%3 for x in b))
        image.append(element)
        norm=field.power(element,121)
        assert not any(norm[1:])
        assert value(ordinary,point)==value(reduced,point)==norm[0]
        assert bool(norm[0])==any(point)
    assert len(set(image))==81
    for element in product(range(3),repeat=5):
        assert field.power(element,243)==element
        if any(element):assert field.power(element,242)==(1,0,0,0,0)
    assert all(value(reduced,tuple(-x%3 for x in p))==-value(reduced,p)%3 for p in points)
    # Identity f² = indicator(nonzero) in the full F3 function ring.
    packed={sum(e<<(4*i) for i,e in enumerate(es)):c for es,c in reduced.items()}
    zero_indicator={0:1}
    for i in range(4):zero_indicator=native.multiply(zero_indicator,{0:1,2<<(4*i):2})
    nonzero_indicator={0:1};native.add_into(nonzero_indicator,zero_indicator,-1)
    assert native.multiply(packed,packed)==nonzero_indicator

    forms={int(c):{int(v):a for v,a in f.items()} for c,f in model['normalized_color_linear_forms'].items()}
    windows,_,_=native.geometry()
    # Enumerate all pair supports, then one ascending-variable shape per
    # low-support class (at most 12 nonzero linear coefficients).
    classes={}
    for a,b in combinations(range(81),2):
        differences=[]
        for x,y in zip(windows[a],windows[b]):
            q=forms[x].copy();native.add_into(q,forms[y],-1);differences.append(q)
        if sum(map(len,differences))>12:continue
        variables=sorted(set().union(*differences));idx={v:i for i,v in enumerate(variables)}
        shape=tuple(tuple((idx[v],c) for v,c in sorted(f.items())) for f in differences)
        classes.setdefault(shape,(a,b,differences))
    assert len(classes)==8
    selections=[]
    for a,b,differences in classes.values():
        best_pair=None
        for perm in permutations(range(4)):
            for signs in product((1,2),repeat=4):
                h=signed_permute(reduced,perm,signs)
                expanded=compose(h,differences)
                item=(len(expanded),perm,signs,expanded,h)
                if best_pair is None or item[:3]<best_pair[:3]:best_pair=item
        selections.append((best_pair[0],a,b,*best_pair[1:],differences))
    chosen=min(selections,key=lambda x:x[:5])
    count,a,b,perm,signs,expanded,h,differences=chosen
    assert (count,a,b,perm,signs)==(179,0,3,(1,0,3,2),(1,1,2,1))
    constraint=expanded.copy();native.add_into(constraint,{0:2})
    assert len(constraint)==180
    # The corresponding embedding basis in original T,L,M,R order.
    embedding=[None]*4
    for i,j in enumerate(perm):embedding[j]=tuple(signs[i]*v%3 for v in basis[i])
    assert reduce_poly(field.norm_poly(embedding))==h
    values=[value(h,p) for p in points]
    assert Counter(values)==Counter({0:1,1:40,2:40})

    new_to_old=order['new_index_to_old_index']+[96]
    old_to_new=order['old_index_to_new_index']+[96]
    assert sorted(new_to_old)==list(range(97))
    assert all(new_to_old[old_to_new[i]]==i for i in range(97))
    assert new_to_old[95:]==[95,96]
    renamed={ordering.remap_word(t,old_to_new):c for t,c in constraint.items()}
    s_field={3<<(4*96):1,1<<(4*96):2}
    s_sign={2<<(4*96):1,0:2}
    # Ordinary identity s³-s = s(s²-1), no field reduction.
    assert {t+(1<<(4*96)):c for t,c in s_sign.items()}==s_field
    base=ordering.parse_polynomials(source_raw.decode());assert len(base)==176
    extra=[s_field,s_sign,constraint]
    full=base+extra
    assert len(full)==179
    def ms(polynomials):
        return ','.join(f'x{i+1}' for i in range(97))+'\n3\n'+',\n'.join(native.expression(p) for p in polynomials)+'\n'
    text=ms(full)
    minfill_polys=[{ordering.remap_word(t,old_to_new):c for t,c in p.items()} for p in full]
    minfill_text=ms(minfill_polys)
    assert all({ordering.remap_word(t,new_to_old):c for t,c in changed.items()}==p for p,changed in zip(full,minfill_polys))
    for i in range(96):assert base[i]=={3<<(4*i):1,1<<(4*i):2}
    assert all(not t>>(4*95) for p in base[96:] for t in p)
    assert all(not t>>(4*95) for t in constraint)
    assert all(len({sum(e for _,e in native.unpack(t))%2 for t in p})==1 for p in base[96:])

    # Original-color records are bilinear, never mislabeled linear forms.
    actual={}
    for cell,f in forms.items():
        p={1<<(4*95):1}
        for v,c in f.items():p[(1<<(4*v))+(1<<(4*96))]=c
        actual[str(cell)]=native.polynomial_record('original-color:'+str(cell),p)
    fixtures=json.loads((HERE/'exact_structure_gauge_certificate.json').read_text())['boards']
    for fixture_index,entry in enumerate(fixtures):
        z=list(map(int,entry['flat']));offset=z[0];D=[(x-offset)%3 for x in z]
        assert len({tuple(z[c] for c in w) for w in windows})==81
        delta=[(D[x]-D[y])%3 for x,y in zip(windows[a],windows[b])]
        sign=value(h,delta);assert sign in (1,2)
        d=[sign*x%3 for x in D]
        prefix=[];acc=0
        for cell in model['original_cell_order']:acc=(acc+d[cell])%3;prefix.append(acc)
        point=[prefix[j] for j in model['free_normalized_prefix_variables']]+[offset,sign]
        if fixture_index<5:assert all(native.evaluate(p,point)==0 for p in full)
        assert all(native.evaluate(p,point)==0 for p in extra)
        assert all(native.evaluate({int(t,16):c for c,t in rec['terms']},point)==z[int(cell)] for cell,rec in actual.items())
        # Six independent affine palettes reconstruct exactly six boards;
        # canonical coupled coordinates remain unchanged.
        reconstructions=[]
        for aa,ss in product(range(3),(1,2)):
            q=point[:95]+[aa,ss]
            board=[(aa+ss*x)%3 for x in d]
            assert q[:95]==point[:95]
            assert all(native.evaluate(p,q)==0 for p in [base[95]]+extra)
            assert all(native.evaluate({int(t,16):c for c,t in rec['terms']},q)==board[int(cell)] for cell,rec in actual.items())
            DD=[(x-board[0])%3 for x in board]
            assert value(h,[(DD[x]-DD[y])%3 for x,y in zip(windows[a],windows[b])])==ss
            reconstructions.append(tuple(board))
        assert len(set(reconstructions))==6

    common={
      'format':'t-board-natural-f3-sign-factor-v1','coefficient_characteristic':3,
      'coefficient_field':'F3','ring_type':'ordinary polynomial ring',
      'variables':97,'coupled_variables':95,'generators':179,
      'scope':'full labeled ternary boards, with translation and sign factors retained internally',
      'count_divisor':1,'count_multiplier':1,'full_count_status':'UNEVALUATED; no solver',
      'prefix':'','fixed_original_cells':[],
      'coupled_canonical_condition':'normalized apex d0=0 and selector(pattern0(d)-pattern3(d))=1',
      'independent_offset_index':95,'independent_sign_index':96,
      'independent_factors':'F3[a]/(a^3-a) tensor F3[s]/(s^2-1)',
      'sign_field_equation':'s^3-s also retained; redundant because s^3-s=s(s^2-1)',
      'original_color_reconstruction':'z_cell=a+s*d_cell (bilinear)',
      'inverse_reconstruction':'a=z_apex; D=z-a; s=selector(pattern0(D)-pattern3(D)); d=s*D; take Gray prefixes of d',
      'original_prefix_reconstruction':'Y_j=s*u_j+(j+1)*a modulo 3',
      'source_translation_model_sha256':sha(model_raw),'source_augmented_input_sha256':sha(source_raw),
      'source_order_metadata_sha256':sha(order_raw),
      'original_cell_order':model['original_cell_order'],
      'free_canonical_prefix_indices':model['free_normalized_prefix_variables'],
      'selector_placement_indices':[a,b],'selector_placement_cells':[list(windows[a]),list(windows[b])],
      'selector_role_order':['T','L','M','R'],
      'selector_terms':[{'coefficient':c,'exponents':list(e)} for e,c in sorted(h.items())],
      'selector_expression':expression(h,('D_T','D_L','D_M','D_R')),
      'field_modulus_low_to_high':modulus,'embedding_basis_by_role':embedding,
      'original_norm_homogeneous_terms':record_tuple(field.norm_poly(embedding)),
      'norm_exponent':121,'norm_identity':'N(L)=product_(k=0..4) L^(3^k), as product of five conjugate linear forms',
      'domain_count':97,'moment_count':76,'e3_count':4,'extra_selector_count':1,'extra_sign_square_count':1,
      'monomial_encoding':'[coefficient,hex integer]; ordinary exponent of variable i occupies bits4i..4i+3',
      'exact_total_claimed':False,
    }
    model_out=dict(common,variable_order='original translated order, then sign',
       normalized_color_linear_forms=model['normalized_color_linear_forms'],
       original_color_bilinear_polynomials=actual,
       selector_zero_polynomial=native.polynomial_record('selector-minus-one',constraint),
       additional_equations=[native.polynomial_record(label,p) for label,p in zip(('sign-field','sign-square','selector-minus-one'),extra)],
       input_file='exact_f3_sign_model.ms',input_sha256=sha(text.encode()))
    renamed_forms={str(c):{str(old_to_new[int(v)]):coef for v,coef in f.items()} for c,f in model['normalized_color_linear_forms'].items()}
    renamed_actual={c:native.polynomial_record(rec['label'],{ordering.remap_word(int(t,16),old_to_new):coef for coef,t in rec['terms']}) for c,rec in actual.items()}
    minfill_out=dict(common,variable_order='frozen minimum-fill renamed translated order, then sign',
       new_index_to_old_index=new_to_old,old_index_to_new_index=old_to_new,
       normalized_color_linear_forms=renamed_forms,original_color_bilinear_polynomials=renamed_actual,
       selector_zero_polynomial=native.polynomial_record('selector-minus-one',renamed),
       additional_equations=[native.polynomial_record(label,{ordering.remap_word(t,old_to_new):c for t,c in p.items()}) for label,p in zip(('sign-field','sign-square','selector-minus-one'),extra)],
       input_file='exact_f3_sign_minfill.ms',input_sha256=sha(minfill_text.encode()))
    audit={
      'status':'PASS','scope':'finite-field polynomial construction, exact model factorization and symbolic exports; no solver',
      'irreducible_degree5_moduli_checked':len(irreducibles()),'initial_coordinate_bases_checked':len(candidates),
      'local_search_start_count':24,'local_search_shear_candidates':search_trials,
      'selected_initial_basis_indices':list(initial_indices),'selected_shears':shears,
      'sparsity_search_scope':'deterministic local elementary-shear descent; no global minimum claim',
      'embedding_distinct_values':len(set(image)),'field_elements_checked':243,
      'all81_selector_values_checked':True,'selector_value_histogram':dict(sorted(Counter(values).items())),
      'selector_square_identity_verified':True,'oddness_verified':True,
      'selector_terms':len(h),'selector_degrees':dict(sorted(Counter(sum(e) for e in h).items())),
      'ordinary_homogeneous_norm_terms':len(ordinary),
      'low_support_pair_shape_classes':len(classes),'signed_permutations_per_class':384,
      'selected_pair':[a,b],'selector_delta_forms':differences,
      'expanded_selector_terms':len(expanded),'expanded_constraint_terms':len(constraint),
      'expanded_constraint_variable_support':sorted(set(v for t in constraint for v,e in native.unpack(t))),
      'expanded_constraint_degrees':dict(sorted(Counter(sum(e for _,e in native.unpack(t)) for t in constraint).items())),
      'candidate_pair_best_terms':[{'pair':[aa,bb],'terms':cc} for cc,aa,bb,*_ in selections],
      'all176_source_generators_preserved':True,'all97_field_domains_retained':True,
      'sign_field_redundancy_ordinary_identity_checked':True,'both_independent_variables_absent_from_coupled_equations':True,
      'full_minfill_inverse_rename_checked':True,'existing_valid_boards_roundtripped':len(fixtures),
      'all179_polynomials_evaluated_on_canonical_boards':5,
      'all_source_coupled_polynomials_have_uniform_degree_parity':True,
      'six_affine_palette_reconstructions_per_board_checked':True,
      'count_divisor':1,'count_multiplier':1,'full_count_status':'UNEVALUATED',
    }
    files={'exact_f3_sign_model.ms':text,'exact_f3_sign_minfill.ms':minfill_text,
           'exact_f3_sign_model.json':json.dumps(model_out,indent=2)+'\n',
           'exact_f3_sign_minfill.json':json.dumps(minfill_out,indent=2)+'\n'}
    audit['export_sha256']={name:sha(data.encode()) for name,data in files.items()}
    audit['generator_sha256']=sha(Path(__file__).read_bytes())
    files['exact_f3_sign_audit.json']=json.dumps(audit,indent=2)+'\n'
    return files,audit


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    files,audit=build()
    for name,data in files.items():
        path=HERE/name
        if args.check:assert path.read_text()==data,name
        else:path.write_text(data)
    print(json.dumps({k:audit[k] for k in ('status','selector_terms','expanded_constraint_terms','existing_valid_boards_roundtripped','export_sha256')},indent=2))
if __name__=='__main__':main()
