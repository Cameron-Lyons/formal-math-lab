"""Search quartic x(u) on several Pell conics, allowing mixed y(u,v), z(u,v).

Run with uv run --with python-flint==0.9.0 python even_abscissa_search.py.
"""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import product
from math import gcd, isqrt

from flint import fmpq_poly, nmod_poly
from quartic_rational_search import admissible_pairs


def chart(t, D):
    L = 1-D*t**2
    return L, [(2*D*t**2)**i * L**(4-i) for i in range(1,5)]


def search(seed, height, discriminants):
    x0, y0, z0 = seed
    assert z0 == 1 and x0**3+y0**2+1 == 2
    primes = [p for p in (5,7,3,11,13,17,19,23) if (2-x0**3) % p]
    all_bits = (1 << len(discriminants))-1
    charts = {}
    bits = {}
    for p in primes:
        nonsquare = next(a for a in range(2,p) if pow(a,(p-1)//2,p) != 1)
        for D in (1,nonsquare):
            L,basis = chart(nmod_poly([0,1],p), D)
            charts[p,D] = x0*L**4,2*L**12,basis
        for j,D in enumerate(discriminants):
            representative = (0 if D%p==0 else
                              1 if pow(D,(p-1)//2,p)==1 else nonsquare)
            bits[p,representative] = bits.get((p,representative),0) | (1<<j)

    @lru_cache(maxsize=200000)
    def local_mask(p, coefficients):
        allowed = bits.get((p,0),0)
        for (prime,D),mask in bits.items():
            if prime != p or D == 0:
                continue
            constant,target,basis = charts[p,D]
            X = constant+sum(a*f for a,f in zip(coefficients,basis))
            if next(admissible_pairs(target-X**3, y0%p),None) is not None:
                allowed |= mask
        return allowed

    rational_charts = {D:chart(fmpq_poly([0,1]),D) for D in discriminants}
    counts = Counter()
    values = range(-height,height+1)
    for d in range(1,height+1):
        tests = [(p,pow(d,-1,p)) for p in primes if d%p]
        for row in product(values,repeat=4):
            if row[-1] == 0 or gcd(d,*row) != 1:
                continue
            counts['abscissas'] += 1
            allowed = all_bits
            for p,inv in tests:
                allowed &= local_mask(p,tuple(a*inv%p for a in row))
                if not allowed:
                    break
            while allowed:
                bit = allowed & -allowed
                allowed -= bit
                D = discriminants[bit.bit_length()-1]
                L,basis = rational_charts[D]
                X = x0*L**4+sum(a*f for a,f in zip(row,basis))/d
                counts['exact_tests'] += 1
                for Y,Z in admissible_pairs(2*L**12-X**3,y0):
                    assert Z**2+Y**2*Z+X**3 == 2*L**12
                    counts['identities'] += 1
                    print('EXACT',seed,D,X,Y,Z,flush=True)
        print('completed denominator',d,'at',seed,dict(counts),flush=True)
    return counts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--height',type=int,default=6)
    parser.add_argument('--max-D',type=int,default=30)
    args = parser.parse_args()
    ds = [D for D in range(2,args.max_D+1)
          if all(D%(k*k) for k in range(2,isqrt(D)+1))]
    print('squarefree D',ds,flush=True)
    for seed in ((0,1,1),(1,0,1),(-2,3,1)):
        print('total',seed,dict(search(seed,args.height,ds)),flush=True)
