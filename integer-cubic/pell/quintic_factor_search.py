"""Quintic abscissas with z=(2-r³)/a and x=r+qz on Pell conics."""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import product
from math import gcd, isqrt

from flint import fmpq, fmpq_poly, nmod_poly
from flint.utils.flint_exceptions import DomainError


def square_integer(n):
    return n >= 0 and isqrt(n)**2 == n


def possible_leading(D, denominator, c, e):
    # At infinity -q must have square leading coefficient in Q(sqrt(D)).
    # Clear the square denominator in -(c+e/sqrt(D))/denominator.
    a = -c*denominator*D**2
    b = -e*denominator*D
    if not b:
        return a > 0 and (square_integer(a) or square_integer(D*a))
    n = a*a-D*b*b
    if not square_integer(n):
        return False
    return any(square_integer(2*(a+k)) for k in (isqrt(n),-isqrt(n)))


@lru_cache(maxsize=None)
def basis(p,D):
    t = nmod_poly([0,1],p) if p else fmpq_poly([0,1])
    L = 1-D*t**2
    U,V = 2*D*t**2,2*t
    return L,(U,V),(U*L,V*L,U**2,U*V)


def square_test(F):
    try:
        return F.sqrt()
    except (ValueError,DomainError):
        return None


@lru_cache(maxsize=100000)
def r_data(p,D,r0,ra,rb,a):
    L,b,_ = basis(p,D)
    R = r0*L+ra*b[0]+rb*b[1]
    Z = (2*L**3-R**3)/a
    return Z,L**9*(a*L**3-Z),3*R**2*L**8,3*R*Z*L**4


@lru_cache(maxsize=150000)
def q_data(p,D,q0,qa,qb,qc,qe):
    L,_,b = basis(p,D)
    Q = q0*L**2+sum(h*f for h,f in zip((qa,qb,qc,qe),b))
    return Q,Q**2,Q**3


def evaluate(p,D,r,q):
    Z,A,B,C = r_data(p,D,*r,2-r[0]**3)
    Q,QQ,QQQ = q_data(p,D,*q)
    return square_test(A-B*Q-C*QQ-QQQ*Z**2)


def scan(height,max_d,max_D,at_seven=False):
    Ds = [D for D in range(2,max_D+1) if all(D%(k*k) for k in range(2,isqrt(D)+1))]
    vals = range(-height,height+1)
    counts = Counter()
    denominators = (1,7,49) if at_seven else range(1,max_d+1)
    for m in denominators:
        for D in Ds:
            if at_seven and m==1 and D%7:
                continue
            leading = [(c,e) for c,e in product(vals,repeat=2)
                       if possible_leading(D,m,c,e)]
            for r0,x0 in product((-1,0,1,2),(0,1,-2)):
                q0 = x0-r0
                ps = [p for p in (5,7,11,13,17)
                      if (2-r0**3)*m%p and D%p]
                for ra,rb in product(vals,repeat=2):
                    if not (ra or rb):
                        continue
                    for (c,e),qa,qb in product(leading,vals,vals):
                        row = (ra,rb,qa,qb,c,e)
                        if gcd(m,*row)!=1:
                            continue
                        counts['after_leading_square'] += 1
                        for p in ps:
                            inv = pow(m,-1,p)
                            a,b,h,k,i,j = (n*inv%p for n in row)
                            if evaluate(p,D%p,(r0,a,b),(q0,h,k,i,j)) is None:
                                break
                        else:
                            counts['exact_tests'] += 1
                            a,b,h,k,i,j = [fmpq(n,m) for n in row]
                            Y = evaluate(0,D,(r0,a,b),(q0,h,k,i,j))
                            if Y is not None:
                                L,base,_ = basis(0,D)
                                Z = r_data(0,D,r0,a,b,2-r0**3)[0]
                                Q = q_data(0,D,q0,h,k,i,j)[0]
                                X = (r0*L+a*base[0]+b*base[1])*L**4+Q*Z
                                assert Z**2*L**9+Z*Y**2+X**3 == 2*L**15
                                counts['identities'] += 1
                                print('EXACT',r0,x0,D,m,row,X,Y,Z,flush=True)
        print('denominators through',m,dict(counts),flush=True)
    return counts


def reductions_mod_seven(D):
    """Test every nonconstant reduced r and every q of order at most two."""
    p = 7
    translations = [(u,v) for u,v in product(range(p),repeat=2)
                    if (u*u-D*v*v)%p==1]
    quadratics = [q_data(p,D,*q) for q in product(range(p),repeat=5)]
    seen = set()
    counts = Counter()
    for h,ra,rb in product(range(p),repeat=3):
        if not (ra or rb) or (h,ra,rb) in seen:
            continue
        # r=h+ra*u+rb*v. Translate the conic, reflect v, and twist r,q
        # simultaneously by a cube root of 1. Each action preserves the square.
        seen.update((k*h%p,k*(ra*u+rb*v)%p,s*k*(D*ra*v+rb*u)%p)
                    for (u,v),s,k in product(translations,(1,-1),(1,2,4)))
        counts['linear_orbits'] += 1
        r0 = (h+ra)%p
        for a in range(1,p):
            Z,A,B,C = r_data(p,D,r0,ra,rb,a)
            ZZ = Z**2
            for Q,QQ,QQQ in quadratics:
                counts['square_tests'] += 1
                if square_test(A-B*Q-C*QQ-QQQ*ZZ) is not None:
                    counts['squares'] += 1
    assert len(seen)==7*(7**2-1)
    assert counts['linear_orbits']==(17 if D==1 else 14)
    print('nonconstant r mod 7, D =',D,dict(counts),flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--height',type=int,default=2)
    parser.add_argument('--max-d',type=int,default=3)
    parser.add_argument('--max-D',type=int,default=30)
    parser.add_argument('--mod7',action='store_true',
                        help='test both squareclasses at 7, with all constants and seeds')
    parser.add_argument('--at-seven',action='store_true',
                        help='use denominators 7 and 49, also 1 when 7 divides D')
    args = parser.parse_args()
    if args.mod7:
        for D in (1,3):
            reductions_mod_seven(D)
    else:
        print(scan(args.height,args.max_d,args.max_D,args.at_seven))
