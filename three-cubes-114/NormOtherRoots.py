# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.9.0"]
# ///
"""Run `uv run NormOtherRoots.py` to search the other cube roots for B=1 in NormSearch.

For d=A³+114 we already searched z=-A mod d. Given its prime factorization,
we search all roots for 3d ≤ |z| < 51d and all non-seed roots for 51d ≤ |z| < 115d.
"""

from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from itertools import chain
from math import isqrt, prod

from flint import fmpz

from NormSearch import A_MIN, A_MAX, FIRST_J, K, MODULI, WIDTH, masks, recover


@lru_cache(maxsize=32768)
def unity_root(p, e):
    """A nonidentity cube root of unity modulo p^e for primes p = 1 mod 3."""
    q = p**e
    exponent = (q//p)*(p-1)//3
    for base in range(2, p):
        w = pow(base, exponent, q)
        if w != 1:
            assert w**3 % q == 1
            return w
    raise ArithmeticError(f'No nontrivial cube root of unity mod {q}')


def other_roots(d, seed, k):
    """Enumerate all roots except the supplied seed; d is coprime to 3 and k squarefree."""
    assert d % 3 and 0 <= seed < d and pow(seed, 3, d) == k % d
    factors = fmpz(d).factor()
    assert prod(int(p)**e for p, e in factors) == d
    roots = [seed]
    for prime, e in factors:
        assert prime.is_prime()
        p = int(prime)
        if k % p == 0:
            # The given seed proves p|k, p|d implies e=1 for a squarefree k.
            assert e == 1 and k % (p*p) and seed % p == 0
            continue
        if p % 3 == 2:
            continue  # Cubing permutes the units, including at powers of 2.
        q = p**e
        w = unity_root(p, e)
        # On this prime power, choose seed, w*seed, or w²*seed.
        # Both increments preserve the current residue at every other factor.
        cofactor = d//q
        scaled_seed = seed*pow(cofactor, -1, q) % q
        deltas = [cofactor*((scaled_seed*(unit-1)) % q) for unit in (w, w*w % q)]
        roots += [(r+delta) % d for delta in deltas for r in roots]
    assert len(roots) == len(set(roots)) and all(pow(r, 3, d) == k % d for r in roots)
    return roots[1:]


def residuals(d, sign, root, first_j, tables, width=WIDTH):
    t = (-sign*root) % d + first_j*d
    bits = (1 << width)-1
    for q, rows in tables:
        bits &= rows[d % q][t % q]
        if not bits:
            return
    while bits:
        bit = bits & -bits
        yield -sign*(t+(bit.bit_length()-1)*d)
        bits ^= bit


def table_for(k, sign):
    return [(q, masks(q, sign, k)) for q in MODULI]


def validate():
    # Compare all roots to exhaustive modular cubing for small composite moduli,
    # including powers of a split prime and a product with the ramified prime 19.
    for d in chain(range(2, 301), (61**2, 61**3, 19*61**2)):
        if d % 3 == 0:
            continue
        roots = [r for r in range(d) if r**3 % d == K % d]
        if roots:
            assert sorted(other_roots(d, roots[0], K)) == roots[1:]

    # Recover Booker and Sutherland's known k=42 triple via a *different* seed.
    d = 102_980_666_258_459
    seed = 28_902_416_942_381
    tables = table_for(42, -1)
    triples = [xyz for r in other_roots(d, seed, 42)
               for z in residuals(d, -1, r, 100, tables)
               if (xyz := recover(-d, z, 42)) is not None]
    assert triples == [(80_435_758_145_817_515, -80_538_738_812_075_974, 12_602_123_297_335_631)]


def search_block(bounds):
    lo, hi = bounds
    tables = {sign: table_for(K, sign) for sign in (-1, 1)}
    divisors = active = count_roots = 0
    tested_low, tested_high = [], []
    for a in range(lo, hi):
        if a % 3 == 0:
            continue
        d = a**3 + K
        seed = (-a) % d
        roots = other_roots(d, seed, K)
        divisors += 1
        active += bool(roots)
        count_roots += len(roots)
        sign = 1 if d % 3 == 1 else -1
        for root_classes, start, width, tested in (
            ([seed, *roots], 3, FIRST_J-3, tested_low),
            (roots, FIRST_J, WIDTH, tested_high),
        ):
            for r in root_classes:
                for z in residuals(d, sign, r, start, tables[sign], width):
                    xyz = recover(sign*d, z, K)
                    disc = (4*((K-z**3)//(sign*d))-d*d)//3
                    tested.append((sign*d, z, isqrt(disc), xyz))
    return divisors, active, count_roots, tested_low, tested_high


def main():
    validate()
    step = 50_000
    blocks = [(a, min(a+step, A_MAX+1)) for a in range(A_MIN, A_MAX+1, step)]
    divisors = active = count_roots = 0
    rows = {'low': [], 'high': []}
    with ProcessPoolExecutor(max_workers=2) as pool:
        for nd, na, nr, low, high in pool.map(search_block, blocks):
            divisors += nd
            active += na
            count_roots += nr
            rows['low'].extend(low)
            rows['high'].extend(high)
    print('Divisors, divisors with extra roots, extra roots')
    print(divisors, active, count_roots)
    for band, candidates in (('low', (FIRST_J-3)*(divisors+count_roots)), ('high', WIDTH*count_roots)):
        solutions = 0
        for a, z, gap, xyz in rows[band]:
            print('Survivor', band, a, z, gap)
            if xyz is not None:
                print('Solution', *xyz)
                solutions += 1
        print(band, 'candidates, exact tests, solutions:', candidates, len(rows[band]), solutions)


if __name__ == '__main__':
    main()
