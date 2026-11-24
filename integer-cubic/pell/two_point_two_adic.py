"""Check both marked quartic systems over all 2-adic coefficient lattices.

Run with uv run --with z3-solver==4.15.4.0 python two_point_two_adic.py.
Each bit-vector represents a residue modulo the indicated power of two.
See QuarticTwoPoint.md for the valuation reduction to these finite tests.
"""

from fractions import Fraction
from math import gcd

import z3


DEGREES = (4, 3, 6)
SEED = (0, 1, 1)
TARGETS = ((1, 0, -1), (-2, 3, 1))


def poly_sum(*polys):
    return [sum(p[i] for p in polys if i < len(p)) for i in range(max(map(len, polys)))]


def plus(a, b):
    return tuple(poly_sum(p, q) for p, q in zip(a, b))


def convolution(p, q, weight):
    return [sum(p[j]*q[i-j]*weight(i, j) for j in range(max(0, i+1-len(q)), min(i+1, len(p))))
            for i in range(len(p)+len(q)-1)]


def identity(solver, triple, multiply):
    x, y, z = triple
    a, b = plus(multiply(x, multiply(x, x)), multiply(z, plus(z, multiply(y, y))))
    assert len(a) == 13 and len(b) == 12
    solver.add(a[0] == 2, *[v == 0 for v in a[1:] + b])


def original(target, bits):
    # In the original integral basis f(v)+w q(v), w=u-1-v,
    # w vanishes at both marks. Interpolation fixes f at v=0,1.
    def conv(p, q):
        return convolution(p, q, lambda i,j: 1)

    def multiply(f, g):
        a, b = f
        c, d = g
        bd = conv(b, d)
        return (poly_sum(conv(a, c), conv([0, -2, 2], bd)),
                poly_sum(conv(a, d), conv(b, c), conv([-2, -2], bd)))

    s = z3.SolverFor('QF_BV')
    triple = []
    for j, (d, a, b) in enumerate(zip(DEGREES, SEED, target)):
        r = [z3.BitVec(f'r{j}_{i}', bits) for i in range(d-1)]
        q = [z3.BitVec(f'q{j}_{i}', bits) for i in range(d)]
        triple.append((poly_sum([a, b-a], conv([0, -1, 1], r)), q))
    identity(s, triple, multiply)
    return s.check()


def balanced(target, fraction, small):
    # h=k+fraction. The normalized basis is e_i=w^i/2^floor(hi).
    bits = 3
    integer_part_factor = z3.BitVec('H', bits)

    def fl(i):
        return (i*fraction.numerator)//fraction.denominator

    def conv(p, q):
        return convolution(p, q, lambda i,j: 2**(fl(i)-fl(j)-fl(i-j)))

    def shift(p, j):
        # Multiplication by w for j=1 and by w^2/2 for j=2.
        if small:
            assert fraction > Fraction(1, 2)
            factors = [2**(fl(i+j)-fl(i)-int(j == 2)) for i in range(len(p))]
        else:
            # k>=1, so 2^k=2H and 2^(2k-1)=2H^2. Keeping H free
            # covers every integer part in one finite computation.
            H = integer_part_factor
            base = 2*H if j == 1 else 2*H*H
            factors = [base*2**(fl(i+j)-fl(i)) for i in range(len(p))]
        return [0]*j+[c*a for c, a in zip(p, factors)]

    def multiply(f, g):
        a, b = f
        c, d = g
        bd = conv(b, d)
        wbd = shift(bd, 1)
        return (poly_sum(conv(a, c), wbd, shift(bd, 2)),
                poly_sum(conv(a, d), conv(b, c), bd, wbd))

    s = z3.SolverFor('QF_BV')
    triple = []
    active = []
    for j, (d, a, b) in enumerate(zip(DEGREES, SEED, target)):
        pair = []
        for m, constant in enumerate((a, b-a)):
            v = [z3.BitVec(f'c{j}_{m}_{i}', bits) for i in range(1, d-m+1)]
            pair.append([constant, *v])
            active.extend(z3.Extract(0, 0, c) == 1 for i, c in enumerate(v, 1)
                          if i % fraction.denominator == 0)
        triple.append(pair)
    s.add(z3.Or(active))
    # The constant v-component vanishes identically because both marked
    # points solve the cubic and v^2=v at w=0.
    identity(s, triple, multiply)
    return s.check()


def main():
    fractions = [Fraction(j, d) for d in range(1, 7) for j in range(d) if gcd(j, d) == 1]
    for target, bits in zip(TARGETS, (2, 12)):
        assert original(target, bits) == z3.unsat
        print(f'{target}: original basis has no model modulo {2**bits}.', flush=True)
        count = 0
        for f in fractions:
            for small in ([False, True] if f > Fraction(1, 2) else [False]):
                result = balanced(target, f, small)
                assert result == z3.unsat, (target, f, small, result)
                count += 1
        print(f'{target}: all {count} normalized charts have no model modulo 8.', flush=True)


if __name__ == '__main__':
    main()
