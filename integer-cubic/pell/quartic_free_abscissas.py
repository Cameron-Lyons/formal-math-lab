"""Exhaustive bounded abscissas in the full-pole one-mark quartic charts at 7.

Generate abscissa residues modulo 343 using the two free local coordinates,
then test bounded primitive rational vectors with the C++ helper and certify
each survivor by polynomial factorization. The second marked value is free.
"""
import argparse
import json
import subprocess
from collections import Counter
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from flint import fmpq_poly, nmod_mat, nmod_poly

from quartic_free_mark import L, parametrized_digits, reduced_operator, lift_slice
from quartic_rational_search import admissible_pairs, bases, full_mod_five
from quartic_rational_slices import SmoothSlice
from fractions import Fraction


def abscissas(record):
    def extract(triple):
        return tuple(int(triple[0][i]) % 343 for i in range(1,9))
    if record['rank'] == 24:
        chart = SmoothSlice(record, 3, 1)
        a,b = record['y'][1:3]
        for i,j in product(range(49),repeat=2):
            yield extract(chart.lift(Fraction(a+7*i),Fraction(b+7*j)))
        return
    free,unknown,discs = parametrized_digits(record)
    for (values,pullback),(base,M) in discs.items():
        if pullback:continue
        operator=reduced_operator(M)
        def get(i,j):
            v=[Fraction(a+49*k) for a,k in zip(values,(i,j))]
            return extract(lift_slice(base,operator,free,unknown,v,3))
        r=get(0,0)
        v=[(a-b)%343 for a,b in zip(get(1,0),r)]
        w=[(a-b)%343 for a,b in zip(get(0,1),r)]
        assert all(a%49==0 for a in v+w)
        for i,j in product(range(7),repeat=2):
            x=tuple((c+i*d+j*e)%343 for c,d,e in zip(r,v,w))
            if (i,j)==(3,5):assert x == get(i,j)
            yield x


def all_residues():
    root=pow(2,49,343)
    rows=set()
    records=Path(__file__).with_name('quartic_orbits_mod7.jsonl').read_text().splitlines()
    for line in records:
        rec=json.loads(line)
        normalized=set(abscissas(rec))
        for i,sgn in product((1,root,root*root%343),(1,-1)):
            rows.update(tuple(i*a*(sgn if j%2==0 else 1)%343 for j,a in enumerate(r))
                        for r in normalized)
        print(rec['x'],len(normalized),'abscissa residues before symmetry',flush=True)
    return rows


def change_basis(rows,basis,mod):
    A=nmod_mat([[int(f[i]) for f in basis] for i in range(1,9)],mod).inv()
    # Matrix/matrix multiplication batches independent coordinate changes.
    rows=list(rows)
    for h in range(0,len(rows),4096):
        block=nmod_mat([list(r) for r in rows[h:h+4096]],mod)*A.transpose()
        yield from (tuple(map(int,r)) for r in block.tolist())


def write_rows(path,rows):
    with path.open('w') as f:
        for r in rows: print(*r,file=f)


def check(height):
    assert 1<=height<=171
    rows=all_residues()
    good5=full_mod_five()
    here=Path(__file__).resolve().parent
    t=nmod_poly([0,1],3)
    target3=2*(1-3*t**2)**12
    good3=[c for c in product(range(3),repeat=8)
           if next(admissible_pairs(target3-nmod_poly([0,*c],3)**3),None) is not None]
    with TemporaryDirectory() as work:
        w=Path(work)
        exe=w/'sieve'
        subprocess.run(['c++','-std=c++17','-O3',str(here/'quartic_free_abscissas.cpp'),'-o',str(exe)],check=True)
        for name,basis in bases().items():
            write_rows(w/'r7',change_basis(rows,basis,343))
            write_rows(w/'r5',change_basis(good5,basis,5))
            # The Pell change of basis is singular at 3, so test the forward map.
            B=nmod_mat([[int(f[i]) for i in range(1,9)] for f in basis],3)
            g3=set(good3)
            c3=list(product(range(3),repeat=8)); A=nmod_mat([list(a) for a in c3],3)*B
            write_rows(w/'r3',(a for a,r in zip(c3,A.tolist()) if tuple(map(int,r)) in g3))
            subprocess.run([str(exe),str(height),str(w)],check=True)
            check_exact(w/'out',basis,name)


def check_exact(path,basis,name):
    primes=(13,11,17,19)
    cache={p:{} for p in primes}
    bp={p:[nmod_poly(list(map(int,f)),p) for f in basis] for p in primes}
    rhs={p:2*(1-3*nmod_poly([0,1],p)**2)**12 for p in primes}
    counts=Counter()
    with path.open() as f:
        for line in f:
            d,*a=map(int,line.split()); counts['after_3_and_5']+=1
            for p in primes:
                if d%p==0:continue
                inv=pow(d,-1,p); key=tuple(c*inv%p for c in a)
                if key not in cache[p]:
                    X=sum(c*b for c,b in zip(key,bp[p]))
                    cache[p][key]=next(admissible_pairs(rhs[p]-X**3),None) is not None
                if not cache[p][key]:break
            else:
                counts['exact_tests']+=1
                X=fmpq_poly(sum(c*b for c,b in zip(a,basis)))/d
                for Y,Z in admissible_pairs(2*fmpq_poly(L)**12-X**3):
                    assert X**3+Z*Y**2+Z**2 == 2*fmpq_poly(L)**12
                    counts['identities']+=1
                    print('EXACT:', X,Y,Z,flush=True)
    print(name,dict(counts),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--height',type=int, default=100)
    check(parser.parse_args().height)
