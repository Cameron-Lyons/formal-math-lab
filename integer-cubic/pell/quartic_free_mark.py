"""Separate 7-adic pullbacks from the other quartic branches through (0,1,1).

Run with uv run --with python-flint==0.9.0 python quartic_free_mark.py.
Use --height to search rational slices with no second-point constraint.
"""

import argparse
import json
from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path

from flint import fmpq_poly, fmpz_mat, fmpz_poly, nmod_mat

from quartic_first_lifts import DEGREES, P, QuarticLifts, T, residual, translate
from quartic_rational_slices import grid, reconstruct


L = 1-3*T**2
INDEX = [(j, i) for j, d in enumerate(DEGREES) for i in range(1, d+1)]


def sparse_parameters():
    # Normalization x=3s^4+bs. The unknowns are b,c,f,e.
    b, c, f, e = v = (0, 3, -2, 2)
    error = [b**3+2*c+3*f, 3*e+(f+c)**2+9*b*b, 2*(f+c)*e+c*c*f+27*b,
             e*e+c*c*e+27]
    jac = nmod_mat([[3*b*b,2,3,0], [18*b,2*(f+c),2*(f+c),3],
                    [27,2*e+2*c*f,2*e+c*c,2*(f+c)], [0,2*c*e,0,2*e+c*c]], P)
    assert jac.det()
    dig = jac.inv()*nmod_mat([[-h//P] for h in error], P)
    return tuple((a+P*int(k)) % P**2 for a,k in zip(v,dig.entries()))


def pullback_pair(c, d):
    b, a, f, e = sparse_parameters()
    s = c*T+d*T**2
    triple = (3*s**4+b*s*L**3, L**3+a*s**3, L**6+f*s**3*L**3+e*s**6)
    return tuple(tuple(int(pol[i]) % 49 for i in range(m+1)) for pol,m in zip(triple,DEGREES))


def jacobian(triple, unknown):
    x,y,z = triple
    ds = (3*x*x, 2*z*y, y*y+2*z)
    cols = [ds[j]*T**i for j,i in unknown]
    return fmpz_mat([[int(col[k]) for col in cols] for k in range(1,25)])


def canonical(triple):
    return tuple(tuple(int(f[i]) % 49 for i in range(n+1)) for f,n in zip(triple,DEGREES))


def digit_triples(record):
    sys = QuarticLifts(tuple(record[k] for k in 'xyz'))
    for ds in sys.surviving_digits():
        out = sys.first
        for a, v in zip(ds, sys.directions):
            if a:
                out = translate(out, 7*a, v)
        yield canonical(out)


def v7(a):
    assert a
    k = 0
    while a % 7 == 0:
        k += 1
        a //= 7
    return k


def reduced_operator(M):
    # If v_7(det M) equals its mod-7 corank four, all elementary divisors
    # divide 7 in Z_7. FLINT returns M^{-1}=N/d with integral matrix N.
    N, d = M.inv().numer_denom()
    d = int(d)
    assert d % 7 == 0 and (d//7) % 7
    unit = pow(d//7, -1, 49)
    R = nmod_mat([[int(a)*unit % 49 for a in row] for row in N.tolist()], 49)
    J = nmod_mat([[int(a) % 49 for a in row] for row in M.tolist()], 49)
    assert all(JR == (7 if i==j else 0) for i,row in enumerate((J*R).tolist())
               for j,JR in enumerate(row))
    return R


def parametrized_digits(record, verify=True):
    c, d = record['polynomial_pullback_cd']
    free = (3,4) if c else (5,6)
    unknown = [key for key in INDEX if key not in [(1,i) for i in free]]
    composed = {pullback_pair(c+7*i, d+7*j) for i,j in product(range(7), repeat=2)}
    assert len(composed) == 49
    desc = {}
    for row in digit_triples(record):
        key = tuple(row[1][i] for i in free)
        branch = row in composed
        triple = tuple(fmpz_poly(list(f)) for f in row)
        M = jacobian(triple, unknown)
        if verify:
            assert nmod_mat([[int(a) for a in r] for r in M.tolist()],7).rank() == 20
            assert v7(int(M.det())) == 4
        assert (key,branch) not in desc
        desc[key,branch] = (triple,M)
    assert all((tuple(a[1][i] for i in free),True) in desc for a in composed)
    assert sum(k[1] for k in desc)==49
    return free,unknown,desc


def lift_slice(triple, operator, free, unknown, values, precision):
    """A constant inverse modulo 49 gains at least one digit per iteration."""
    mod = 7**(precision+1)
    x,y,z = (fmpz_poly(f) for f in triple)
    for i,a in zip(free, values):
        y[i] = a.numerator*pow(a.denominator,-1,mod) % mod
    out = (x,y,z)
    # Initially F=0 mod 49. Find a correction of size 49 using the ordinary
    # Jacobian; the divided inverse requires an initial residual divisible by 343.
    E = residual(out)
    rr = [-int(E[i])//49 % 7 for i in range(1,25)]
    assert all(int(k)%49==0 for k in E)
    M = jacobian(triple,unknown)
    aug = nmod_mat([list(map(int,row))+[v] for row,v in zip(M.tolist(),rr)],7)
    rrmat,rank=aug.rref()
    assert rank==20
    for j in range(rank):
        pivot=next(i for i in range(24) if rrmat[j,i])
        l,deg=unknown[pivot]
        out[l][deg]+=49*int(rrmat[j,24])
    m=343
    for _ in range(3, precision+1):
        E=residual(out)
        assert all(int(k)%m==0 for k in E)
        rr=nmod_mat([[-int(E[i])//m % 49] for i in range(1,25)],49)
        for (j,i),v in zip(unknown,(operator*rr).entries()):
            out[j][i]+=(m//7)*int(v)
        m*=7
    assert all(int(k)%m==0 for k in residual(out))
    return out


def search(record, free, unknown, domains, height, coefficient_height, precision):
    c=record['polynomial_pullback_cd'][0]
    if not c:
        return 0,[]
    generators=[grid(height, record['y'][i]) for i in free]
    operators={}
    hits=[]
    count=0
    mod=7**precision
    assert mod>2*coefficient_height**2
    root=pow(2,7**(precision-1),mod)
    assert pow(root,3,mod)==1 and root%7==2
    for values in product(*generators):
        key=tuple(v.numerator*pow(v.denominator,-1,49)%49 for v in values)
        base,M=domains[key,False]
        if key not in operators:
            operators[key]=reduced_operator(M)
        x,y,z=lift_slice(base,operators[key],free,unknown,values,precision)
        count+=1
        def recon(f,a=1):
            coeffs=[reconstruct(a*int(k)%mod,mod,coefficient_height) for k in f]
            return None if any(v is None for v in coeffs) else fmpq_poly(coeffs)
        yy=recon(y)
        if yy is None:continue
        zz=recon(z)
        if zz is None:continue
        for a in (1,root,root**2%mod):
            xx=recon(x,a)
            if xx is not None and xx**3+zz*yy**2+zz**2==2*fmpq_poly(L)**12:
                hits.append((str(xx),str(yy),str(zz)))
    return count,hits


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--height',type=int,default=0)
    parser.add_argument('--coefficient-height',type=int,default=10**18)
    parser.add_argument('--precision',type=int,default=46)
    args=parser.parse_args()
    records=map(json.loads, Path(__file__).with_name('quartic_orbits_mod7.jsonl').read_text().splitlines())
    totals=Counter()
    for r in records:
        even_x = not any(r['x'][1::2])
        if even_x:
            assert r['rank'] == 20
        if r['rank']!=20:continue
        free,unk,domains=parametrized_digits(r)
        n=len(domains)-49
        if even_x:
            # Every remaining lift in this case has nonzero linear term
            # modulo 49. Twisting x or replacing t by -t preserves that.
            assert all(int(row[0][1])%49 for (_,composed),(row,_) in domains.items()
                       if not composed)
        print(f"c,d={r['polynomial_pullback_cd']}, fixed y indices {free}: 49 pullbacks, {n} other classes",flush=True)
        totals['all_children']+=r['orbit']*len(domains)
        totals['pullback']+=r['orbit']*49
        if args.height:
            count,hits=search(r,free,unk,domains,args.height,args.coefficient_height,args.precision)
            totals['slices']+=count
            totals['identities']+=len(hits)
            if hits: print(hits,flush=True)
    print(dict(totals))


if __name__=='__main__':main()
