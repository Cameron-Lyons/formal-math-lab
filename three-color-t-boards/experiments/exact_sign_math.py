#!/usr/bin/env python3
"""Reproduce/check signed-count obstructions using existing certificates only."""
from functools import reduce
from itertools import permutations,product
from pathlib import Path
import argparse
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PALETTES=tuple(permutations(range(3)))
CANONICAL_CERT_SOURCES=[('published',3),('published',4)]+[
    ('extended',i) for i in (5,6,7,8,10,13,17,18,19,21,23,26,28,30,32,33,
    36,38,39,40,45,48,50,57,60,61,62,64,65,68,70,72,73,75,76,78,79,80,
    82,84,87,90,91,94,95,99,100,101,104,106,108,113,115,121)]


def reflection(flat):
    return ''.join(flat[r*r:(r+1)**2][::-1] for r in range(10))


def recolor(flat,palette):
    return ''.join(str(palette[int(c)]) for c in flat)


def canonical(flat):
    return min(recolor(s,p) for s in (flat,reflection(flat)) for p in PALETTES)


def sign(permutation):
    n=len(permutation);assert sorted(permutation)==list(range(n))
    inversions=sum(permutation[i]>permutation[j] for i in range(n) for j in range(i+1,n))
    visited=set();cycles=0
    for start in range(n):
        if start in visited:continue
        cycles+=1;i=start
        while i not in visited:
            visited.add(i);i=permutation[i]
    assert inversions%2==(n-cycles)%2
    return (-1)**inversions,inversions


def board_data(flat):
    assert len(flat)==100 and set(flat)<=set('012')
    labels=[];triples=[];rotors=[[] for _ in range(27)]
    for r in range(1,10):
        for j in range(2*r-1):
            t,l,m,o=(int(flat[cell]) for cell in ((r-1)**2+j,r*r+j,r*r+j+1,r*r+j+2))
            triple=9*t+3*l+m;labels.append(3*triple+o)
            triples.append(triple);rotors[triple].append(o)
    epsilon,inversions=sign(labels)
    rotor_sign=1
    for rotor in rotors:
        rotor_sign*=sign(rotor)[0]
    shuffle_inversions=sum(triples[i]>triples[j] for i in range(81) for j in range(i+1,81))
    shuffle_sign=(-1)**shuffle_inversions
    assert epsilon==rotor_sign*shuffle_sign
    return {'flat':flat,'rows':[flat[r*r:(r+1)**2] for r in range(10)],
            'pattern_sign':epsilon,'pattern_inversions':inversions,
            'rotor_sign_product':rotor_sign,'triple_shuffle_sign':shuffle_sign,
            'rotor_boundary':flat[0]+''.join(flat[r*r:r*r+2] for r in range(1,10)),
            'bottom_row':flat[81:],'already_canonical':canonical(flat)==flat,
            'rotor_orders':[''.join(map(str,r)) for r in rotors]}


def full_indicator_row(flat):
    return 1 | sum(1<<(1+3*cell+int(color)) for cell,color in enumerate(flat))


def build():
    published_path=ROOT/'sources/anc/certificates.json'
    extended_path=ROOT/'extended_seeds.json'
    sources={'published':[''.join(rows) for rows in json.loads(published_path.read_text())['ternary_seeds']],
             'extended':[''.join(entry['rows']) for entry in json.loads(extended_path.read_text())]}
    base=sources['published'][0]
    orbit=[]
    for reflected in (False,True):
        for k in range(3):
            p=tuple((c+k)%3 for c in range(3))
            s=recolor(reflection(base) if reflected else base,p)
            orbit.append(dict(board_data(s),source=['published',0],cyclic_shift=k,reflected=reflected))
    pairs={}
    for name,indices in [('canonical_two_cell_pair',(7,8)),('same_boundary_and_bottom_pair',(162,164))]:
        pairs[name]=[dict(board_data(sources['extended'][i]),source=['extended',i]) for i in indices]
    certificate=[dict(board_data(canonical(sources[source][index])),source=[source,index])
                 for source,index in CANONICAL_CERT_SOURCES]
    prior_common=['222012012','00021112200','0010010022200','110202021201011',
                  '02121111210221022','2221101121221000202']
    prior=[board_data(''.join(top+prior_common)) for top in
           [['2','122','11011','1200012'],['2','122','11012','1200011']]]
    return {'format':'t-board-pattern-sign-certificate-v1',
            'placement_order':'row-major upward T; lower rows1..9, start columns0..2r-2',
            'pattern_order':'lexicographic(top,left,middle,right), index27t+9l+3m+r',
            'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in (published_path,extended_path)},
            'universal_six_board_instance':orbit,**pairs,
            'canonical_factor_sign_xor_certificate':certificate,
            'prior_rotor_swap_pair':prior}


def check(document):
    assert document['format']=='t-board-pattern-sign-certificate-v1'
    # Verify every embedded board and every recorded numerical assertion.
    for key in ('universal_six_board_instance','canonical_two_cell_pair',
                'same_boundary_and_bottom_pair','canonical_factor_sign_xor_certificate',
                'prior_rotor_swap_pair'):
        for record in document[key]:
            actual=board_data(record['flat'])
            assert all(record[k]==v for k,v in actual.items())
    palette_signs=[]
    for palette in PALETTES:
        labels=[sum(palette[c]*3**(3-i) for i,c in enumerate(pattern))
                for pattern in product(range(3),repeat=4)]
        palette_signs.append(sign(labels)[0])
    assert palette_signs==[1]*6
    pattern_reflection=[27*t+9*r+3*m+l for t,l,m,r in product(range(3),repeat=4)]
    placement_reflection=[(r-1)**2+2*r-2-j for r in range(1,10) for j in range(2*r-1)]
    assert sign(pattern_reflection)[0]==-1 and sign(placement_reflection)[0]==1

    six=document['universal_six_board_instance']
    assert len(six)==len({record['flat'] for record in six})==6
    assert all(sum(record['flat'][cell]==str(color) for record in six)==2
               for cell in range(100) for color in range(3))
    assert reduce(lambda a,b:a*b,(r['pattern_sign'] for r in six),1)==-1
    for k in range(3):
        assert six[k+3]['flat']==reflection(six[k]['flat'])
        assert six[k+3]['pattern_sign']==-six[k]['pattern_sign']

    a,b=document['canonical_two_cell_pair']
    assert a['already_canonical'] and b['already_canonical']
    assert a['flat'][:81]==b['flat'][:81]
    assert a['rotor_boundary']==b['rotor_boundary']
    assert a['pattern_sign']==-b['pattern_sign']
    differences=[i for i in range(100) if a['flat'][i]!=b['flat'][i]]
    assert differences==[94,96]
    changed_rotors=[i for i in range(27) if a['rotor_orders'][i]!=b['rotor_orders'][i]]
    assert changed_rotors==[18]  # Triple200.
    assert a['triple_shuffle_sign']==b['triple_shuffle_sign']==1

    a,b=document['same_boundary_and_bottom_pair']
    assert a['rotor_boundary']==b['rotor_boundary'] and a['bottom_row']==b['bottom_row']
    assert a['pattern_sign']==-b['pattern_sign']
    assert a['rotor_sign_product']==b['rotor_sign_product']

    certificate=document['canonical_factor_sign_xor_certificate']
    assert len(certificate)==len({r['flat'] for r in certificate})==56
    assert all(r['already_canonical'] for r in certificate)
    coefficient_xor=0;rhs_xor=0
    for record in certificate:
        coefficient_xor^=full_indicator_row(record['flat'])
        rhs_xor^=int(record['pattern_sign']==-1)
    assert coefficient_xor==0 and rhs_xor==1
    # Redundant independent cell/color-count verification of the XOR identity.
    assert all(sum(r['flat'][cell]==str(color) for r in certificate)%2==0
               for cell in range(100) for color in range(3))

    prior=document['prior_rotor_swap_pair']
    assert prior[0]['pattern_sign']==prior[1]['pattern_sign']==-1
    assert prior[0]['rotor_sign_product']==-prior[1]['rotor_sign_product']
    assert prior[0]['triple_shuffle_sign']==-prior[1]['triple_shuffle_sign']
    return {'status':'PASS','all_global_palette_label_signs':palette_signs,
            'pattern_reflection_sign':-1,'placement_reflection_sign':1,
            'universal_six_board_sign_product':-1,
            'canonical_opposite_sign_pair_hamming_distance':2,
            'same19_boundary_and_bottom_opposite_sign_pair':True,
            'canonical_weight_obstruction_boards':56,
            'canonical_coefficient_xor':0,'canonical_sign_rhs_xor':1,
            'prior_rotor_pair_pattern_signs':[-1,-1],
            'new_witness_search_performed':False,'full_count_computed':False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='Verify the saved self-contained certificate only.')
    args=parser.parse_args();path=HERE/'exact_sign_math_certificate.json'
    document=json.loads(path.read_text()) if args.check else build()
    report=check(document)
    if not args.check:path.write_text(json.dumps(document,indent=2)+'\n')
    report['certificate_sha256']=hashlib.sha256(path.read_bytes()).hexdigest()
    (HERE/'exact_sign_math_check_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
