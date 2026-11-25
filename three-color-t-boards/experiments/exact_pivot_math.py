#!/usr/bin/env python3
"""Compare and export alternate exact F2 pivot eliminations; no solver runs."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import argparse
import hashlib
import json
import random

HERE = Path(__file__).resolve().parent
ROLES = ('T','L','M','R')
CELLS = {(j-r,-r): r*r+j for r in range(10) for j in range(2*r+1)}
WINDOWS = []
for x,y in CELLS:
    locations = ((x,y+1),(x-1,y),(x,y),(x+1,y))
    if all(p in CELLS for p in locations):
        WINDOWS.append(tuple(CELLS[p] for p in locations))
assert set(WINDOWS) == {((r-1)**2+j,r*r+j,r*r+j+1,r*r+j+2)
                       for r in range(1,10) for j in range(2*r-1)}
ROLE_SETS = [{w[i] for w in WINDOWS} for i in range(4)]
FIELD_MUL = ((0,0,0,0),(0,1,2,3),(0,2,3,1),(0,3,1,2))


def toggle(poly, term):
    if term in poly: poly.remove(term)
    else: poly.add(term)


def term(pairs):
    powers = Counter()
    for cell,power in pairs: powers[cell] += power
    return tuple(sorted((cell,power%3) for cell,power in powers.items() if power%3))


def frobenius(poly):
    return {term((cell,2*power) for cell,power in t) for t in poly}


def substitutions(pivots):
    if len(set(pivots)) != 4: return None
    rows = [sum(1<<cell for cell in cells) for cells in ROLE_SETS]
    for i,cell in enumerate(pivots):
        j = next((j for j in range(i,4) if rows[j]>>cell&1),None)
        if j is None: return None
        rows[i],rows[j] = rows[j],rows[i]
        for j in range(4):
            if i!=j and rows[j]>>cell&1: rows[j] ^= rows[i]
    result = {}
    for cell,row in zip(pivots,rows):
        row ^= 1<<cell
        assert not any(row>>p&1 for p in pivots)
        result[cell] = tuple(v for v in range(100) if row>>v&1)
    return result


def legal_pivots(pivots):
    return substitutions(pivots) is not None and max(sum(c in pivots for c in w) for w in WINDOWS)<=1


def reduce_moments(pivots):
    assert legal_pivots(pivots)
    sources = substitutions(pivots)
    moments,zero = {},[]
    for exponents in product(range(3),repeat=4):
        if not any(exponents): continue
        poly = set()
        for window in WINDOWS:
            fixed,pivot = [],None
            for cell,power in zip(window,exponents):
                if not power: continue
                if cell in sources:
                    assert pivot is None
                    pivot = cell,power
                else: fixed.append((cell,power))
            if pivot is None: toggle(poly,term(fixed))
            else:
                cell,power = pivot
                for replacement in sources[cell]:
                    toggle(poly,term(fixed+[(replacement,power)]))
        if poly: moments[exponents] = poly
        else: zero.append(exponents)
    assert len(moments)==72 and len(zero)==8
    assert all(sum(v!=0 for v in e)==1 for e in zero)
    for e,p in moments.items():
        assert frobenius(p)==moments[tuple(2*v%3 for v in e)]
    cubes={}
    for cell,linear in sources.items():
        poly={()}
        for a in linear:
            for b in linear: toggle(poly,term(((a,1),(b,2))))
        assert len(poly)==len(linear)*(len(linear)-1)+(len(linear)%2==0)
        cubes[cell]=poly
    return sources,moments,cubes


def e2_reduce(cells,sources):
    poly=set()
    for a,b in combinations(sorted(cells),2):
        for x in sources.get(a,(a,)):
            for y in sources.get(b,(b,)): toggle(poly,term(((x,1),(y,1))))
    return poly


def elementary(sources):
    raw=[e2_reduce(cells,sources) for cells in ROLE_SETS]
    result=[('elementary:e2:T',raw[0])]
    for a,b in ((0,2),(2,1),(2,3)):
        label=f'elementary:e2:diff:{ROLES[a]}:{ROLES[b]}'
        direct=e2_reduce(ROLE_SETS[a]-ROLE_SETS[b],sources)^e2_reduce(ROLE_SETS[b]-ROLE_SETS[a],sources)
        assert direct==raw[a]^raw[b]
        result.append((label,direct))
    return result+[(label+':frobenius',frobenius(p)) for label,p in result]


def metrics(pivots,full=False):
    sources,moments,cubes=reduce_moments(pivots)
    reps={e:p for e,p in moments.items() if next(v for v in e if v)==1}
    out={
        'pivots':list(pivots),'substitution_lengths':[len(sources[p]) for p in pivots],
        'pivot_domain_term_counts':[len(cubes[p]) for p in pivots],
        'moment40_terms':sum(map(len,reps.values())),
        'moment80_terms':sum(map(len,moments.values())),
        'pivot_domain_terms':sum(map(len,cubes.values())),
    }
    out['base40_terms']=out['moment40_terms']+out['pivot_domain_terms']
    out['base80_terms']=out['moment80_terms']+out['pivot_domain_terms']
    if full:
        eqs=elementary(sources)
        out['elementary8_term_counts']=[len(p) for _,p in eqs]
        out['elementary8_degree_histograms']=[{str(d):n for d,n in sorted(Counter(sum(e for _,e in t) for t in p).items())}
                                              for _,p in eqs]
        out['augmented80_terms']=out['base80_terms']+sum(len(p) for _,p in eqs)
    return out


def rank4(vectors):
    pivots={}
    for row in vectors:
        while row:
            p=row.bit_length()-1
            if p in pivots: row ^= pivots[p]
            else:
                pivots[p]=row
                break
    return len(pivots)


def cubic_support_bound():
    supports={}
    for mask in range(1,16):
        cells=set()
        for i,role in enumerate(ROLE_SETS):
            if mask>>i&1: cells ^= role
        supports[mask]=len(cells)
    best=None;minimizers=[];bases=0
    for masks in combinations(range(1,16),4):
        if rank4(masks)!=4:continue
        bases+=1
        lengths=[supports[m]-1 for m in masks]
        cost=sum(n*(n-1)+(n%2==0) for n in lengths)
        if best is None or cost<best:best=cost;minimizers=[list(masks)]
        elif cost==best:minimizers.append(list(masks))
    return {'all_unary_combination_support_sizes':{str(m):n for m,n in supports.items()},
            'independent_four_combination_bases':bases,
            'minimum_pivot_cubic_terms':best,'minimizing_unary_combination_masks':minimizers,
            'scope':'all invertible eliminations of four original cells using the four unary equations'}


def packed(poly,free):
    indices={cell:i for i,cell in enumerate(free)}
    return sorted(sum(power<<(2*indices[cell]) for cell,power in t) for t in poly)


def expression(poly,free):
    indices={cell:i+1 for i,cell in enumerate(free)}
    return '+'.join('*'.join('x'+str(indices[cell])+('^2' if power==2 else '')
                           for cell,power in t) or '1' for t in sorted(poly))


def evaluate(poly,values):
    out=0
    for t in poly:
        v=1
        for cell,power in t:
            for _ in range(power): v=FIELD_MUL[v][values[cell]]
        out ^= v
    return out


def validate_values(pivots,sources,moments,cubes,elem):
    rng=random.Random(sum((i+1)*p for i,p in enumerate(pivots)))
    free=[c for c in range(100) if c not in pivots]
    for _ in range(12):
        values={c:rng.choice((1,2,3)) for c in free}
        for c,linear in sources.items():
            values[c]=0
            for v in linear:values[c]^=values[v]
        for e,poly in moments.items():
            direct=0
            for w in WINDOWS:
                v=1
                for c,power in zip(w,e):
                    for _ in range(power):v=FIELD_MUL[v][values[c]]
                direct^=v
            assert evaluate(poly,values)==direct
        for c,p in cubes.items():
            z=values[c]
            assert evaluate(p,values)==(FIELD_MUL[z][FIELD_MUL[z][z]]^1)
        raw=[]
        for cells in ROLE_SETS:
            value=0
            for a,b in combinations(cells,2):value^=FIELD_MUL[values[a]][values[b]]
            raw.append(value)
        targets=[raw[0],raw[0]^raw[2],raw[2]^raw[1],raw[2]^raw[3]]
        assert [evaluate(p,values) for _,p in elem[:4]]==targets
        assert [evaluate(p,values) for _,p in elem[4:]]==[FIELD_MUL[v][v] for v in targets]
    cert=json.loads((HERE/'exact_structure_gauge_certificate.json').read_text())
    for entry in cert['boards']:
        values={c:int(v)+1 for c,v in enumerate(entry['flat'])}
        for c,linear in sources.items():
            z=0
            for v in linear:z^=values[v]
            assert z==values[c]
        assert all(evaluate(p,values)==0 for p in list(moments.values())+list(cubes.values()))
        assert all(evaluate(p,values)==0 for _,p in elem)
    return {'random_substituted_assignments_checked':12,'existing_valid_boards_checked':len(cert['boards'])}


def export_variant(name,pivots,write):
    sources,moments,cubes=reduce_moments(pivots)
    free=[c for c in range(100) if c not in pivots]
    elem=elementary(sources)
    values_audit=validate_values(pivots,sources,moments,cubes,elem)
    reps=[(e,p) for e,p in moments.items() if next(v for v in e if v)==1]
    assert len(reps)==36
    base=[('moment:'+','.join(map(str,e)),p) for e,p in reps]
    base += [(f'pivot_domain:{p}',cubes[p]) for p in pivots]
    partners=[('moment:'+','.join(str(2*v%3) for v in e),frobenius(p)) for e,p in reps]
    common={
        'coefficient_field':'F2','ring_type':'ordinary polynomial ring','variables':96,
        'free_original_cells':free,'pivot_cells':list(pivots),
        'pivot_substitutions':{str(c):list(linear) for c,linear in sources.items()},
        'free_domain_equations':'z_i^3+1 for all96 free variables',
        'scope':'full labeled ternary boards','prefix':'','symmetry_normalization':False,
        'count_multiplier':1,'count_divisor':1,
        'monomial_encoding':'hex integer: exponent of free variable i in bits2*i,2*i+1; coefficient1; constant0x0',
        'max_pivots_per_T':1,'status':'PREPARED_NOT_RUN; quotient dimension unevaluated',
    }
    files=[]
    def save(suffix,contents):
        path=HERE/f'exact_pivot_math_{name}_{suffix}'
        if write:path.write_text(contents)
        else:assert path.read_text()==contents
        files.append({'file':path.name,'sha256':hashlib.sha256(contents.encode()).hexdigest()})
    for count,eqs in ((40,base),(80,base+partners)):
        document=dict(common,format='t-board-alternative-pivot-fourier-v1',
                      full_moment_count=count,retained_moment_count=count-4 if count==40 else count-8,
                      substituted_pivot_domain_count=4,
                      remaining_equations=[{'label':label,'terms':[hex(t) for t in packed(p,free)]} for label,p in eqs])
        save(f'fourier{count}.json',json.dumps(document,indent=2)+'\n')
        for augmented in (False,True):
            polynomials=[f'x{i+1}^3+1' for i in range(96)]
            polynomials += [expression(p,free) for _,p in eqs+(elem if augmented else [])]
            text=','.join(f'x{i+1}' for i in range(96))+'\n2\n'+',\n'.join(polynomials)+'\n'
            save(f'fourier{count}'+('_e2' if augmented else '')+'.ms',text)
    document=dict(common,format='t-board-alternative-pivot-elementary-v1',augmentation_only=True,
                  generator_groups={'elementary_quadratics':[0,1,2,3],'frobenius_partners_modulo_cubics':[4,5,6,7]},
                  remaining_equations=[{'label':label,'terms':[hex(t) for t in packed(p,free)]} for label,p in elem])
    save('elementary.json',json.dumps(document,indent=2)+'\n')
    return dict(metrics(pivots,True),name=name,files=files,value_audit=values_audit)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    # First independently reproduce every frozen baseline retained generator.
    pivots=(0,81,90,99)
    sources,moments,cubes=reduce_moments(pivots)
    saved=json.loads((HERE/'exact_parity_math_fourier_reduced.json').read_text())
    free=[c for c in range(100) if c not in pivots]
    actual={x['label']:{int(t,16) for t in x['terms']} for x in saved['remaining_equations']}
    expected={'moment:'+','.join(map(str,e)):set(packed(p,free)) for e,p in moments.items()
              if next(v for v in e if v)==1}
    expected.update({f'pivot_domain:{c}':set(packed(p,free)) for c,p in cubes.items()})
    assert actual==expected

    candidates=[]
    for u in range(81):
        p=(u,81,90,99)
        if legal_pivots(p):candidates.append(metrics(p))
    candidates.sort(key=lambda m:(m['base80_terms'],m['pivots']))
    cube_optimal_scan=[]
    for b in range(83,98):
        for upper in ((6,9,15),(12,1,8),(20,4,15),(30,9,24)):
            p=tuple(upper)+(b,)
            if legal_pivots(p):cube_optimal_scan.append(metrics(p))
    cube_optimal_scan.sort(key=lambda m:(m['base80_terms'],m['pivots']))
    selected=[('p6',(6,81,90,99)),('sparse',(6,9,15,90))]
    best=tuple(cube_optimal_scan[0]['pivots'])
    if best not in [p for _,p in selected]:selected.append(('best',best))
    report={
        'status':'PASS','scope':'symbolic size comparison and exact exports; no solver',
        'baseline_reproduced_exactly':True,'baseline':metrics((0,81,90,99),True),
        'all_single_upper_pivot_candidates':candidates,
        'restricted_cubic_optimal_pattern_scan':cube_optimal_scan,
        'cubic_support_lower_bound':cubic_support_bound(),
        'exports':[export_variant(name,p,not args.check) for name,p in selected],
    }
    path=HERE/'exact_pivot_math_audit.json'
    if args.check:assert json.loads(path.read_text())==report
    else:path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({
        'single_upper_candidates':len(candidates),'best_single_upper':candidates[0],
        'restricted_optimal_candidates':len(cube_optimal_scan),'best_restricted':cube_optimal_scan[0],
        'global_cubic_support_bound':report['cubic_support_lower_bound'],
        'exports':[{k:v for k,v in x.items() if k not in ('files','value_audit')} for x in report['exports']],
    },indent=2))


if __name__=='__main__':main()
