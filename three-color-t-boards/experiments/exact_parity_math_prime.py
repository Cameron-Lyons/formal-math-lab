#!/usr/bin/env python3
"""Small exact checks for the inert-prime Fourier formulation; no board search."""
from itertools import product
from math import comb
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def checks(p):
    assert p % 3 == 2 and all(p % d for d in range(2,int(p**0.5)+1))
    def add(z,w):
        return ((z[0]+w[0])%p,(z[1]+w[1])%p)
    def mul(z,w):
        a,b=z; c,d=w
        return ((a*c-b*d)%p,(a*d+b*c-b*d)%p)
    def power(z,n):
        out=(1,0)
        while n:
            if n&1:
                out=mul(out,z)
            z=mul(z,z); n>>=1
        return out
    zero=(0,0); one=(1,0); omega=(0,1)
    colors=(one,omega,((p-1)%p,(p-1)%p))
    assert len(set(colors))==3
    assert all(power(z,3)==one and power(z,p)==power(z,2) for z in colors)
    assert all(add(add(one,z),mul(z,z)) != zero for z in ((a,0) for a in range(p)))
    # Explicit3x3 Fourier inverse: sum_z z^(e-f)=3 if e=f, otherwise0.
    for e,f in product(range(3),repeat=2):
        total=zero
        for z in colors:
            total=add(total,power(z,(e-f)%3))
        assert total==((3%p,0) if e==f else zero)
    diagonal=sum(z==w for z,w in product(colors,repeat=2))
    plus_diagonal=sum(add(z,w)==zero for z,w in product(colors,repeat=2))
    triples=sum(add(add(z,w),v)==zero for z,w,v in product(colors,repeat=3))
    assert diagonal==3 and triples==6
    assert plus_diagonal==(3 if p==2 else 0)
    # Number of abstract nonnegative marginal tables satisfying the residues.
    tables={}
    for roles in range(1,5):
        bins=3**roles; target=3**(4-roles)
        slack=bins*(target//p)
        tables[roles]=comb(slack+bins-1,bins-1)
        assert (tables[roles]==1)==(p>target)
    return {'prime':p,'domain_count':3,'two_domain_count':9,
            'minus_diagonal_count':diagonal,'plus_diagonal_count':plus_diagonal,
            'three_color_sum_zero_count':triples,'fixed_color_two':list(colors[2]),
            'abstract_marginal_tables_by_role_count':tables}


def main():
    source=json.loads((HERE/'exact_parity_math_fourier_original.json').read_text())
    terms=[]
    for equation in source['moment_equations']:
        canonical=[tuple(tuple(pair) for pair in monomial) for monomial in equation['terms']]
        assert len(canonical)==len(set(canonical))==81
        terms.append(len(canonical))
    result={'status':'PASS','prime_checks':[checks(p) for p in (2,5,11,17,23,29,83)],
            'original_json_moments_have_81_distinct_coefficient_one_terms':True,
            'original_json_moment_terms':sum(terms),'full_board_search_performed':False}
    (HERE/'exact_parity_math_prime_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
