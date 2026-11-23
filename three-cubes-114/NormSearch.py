"""Search one cube root for each d = A³ + 114 B³, using only Python's standard library.

For coprime A, B, the class r = -A/B (mod d) satisfies r³ = 114 (mod d).
The search uses every positive d with the stated bounds on A and B and 3 ∤ d.
It tests the elements z of this root class with 51 d ≤ |z| < 115 d and
sign opposite to the signed pair sum x+y. The cutoff at 115 is exclusive.
Pass --survivors to print the rows checked in NormCertificates.lean.
"""

from argparse import ArgumentParser
from math import gcd, isqrt


A_MIN, A_MAX = 600_000, 2_000_000  # inclusive
B_MAX = 128
FIRST_J = 51
WIDTH = 64
MODULI = (27, 32, 7, 5, 13, 11, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
          61, 67, 71, 73, 79, 83, 89, 97)
K = 114


def masks(q, sign, k=K):
    """Build bit masks for 64 values t, t+d, ...; x+y = sign*d and z = -sign*t."""
    cubes = [n**3 % q for n in range(q)]
    rows = []
    for d in range(q):
        a = sign*d % q
        pair_cubes = {(cubes[x] + cubes[(a-x) % q]) % q for x in range(q)}
        permitted = [(k + sign*cubes[t]) % q in pair_cubes for t in range(q)]
        # Doubling from masks of length one yields the desired bit sequence.
        row = list(map(int, permitted))
        width = 1
        while width < WIDTH:
            shift = width*d % q
            row = [mask | (row[(t+shift) % q] << width) for t, mask in enumerate(row)]
            width *= 2
        rows.append(row)
    return rows


def recover(a, z, k=K):
    """Recover an integral pair from its signed sum and the third coordinate."""
    quotient, remainder = divmod(k - z**3, a)
    assert remainder == 0
    diff_sq, remainder = divmod(4*quotient - a*a, 3)
    if remainder or diff_sq < 0:
        return None
    diff = isqrt(diff_sq)
    if diff*diff != diff_sq or (a+diff) % 2:
        return None
    x, y = (a+diff)//2, (a-diff)//2
    assert x**3 + y**3 + z**3 == k
    return x, y, z


def search(a_min=A_MIN, a_max=A_MAX, b_max=B_MAX, show_survivors=False):
    tables = {s: [(q, masks(q, s)) for q in MODULI] for s in (-1, 1)}
    divisors = exact = solutions = 0
    for b in range(1, b_max+1):
        # A³ ≡ d mod B, so d*j ≡ A mod B precisely when A²*j ≡ 1 mod B.
        multipliers = [pow(a*a, -1, b) if gcd(a, b) == 1 else None for a in range(b)]
        norm_term = K*b**3
        for a in range(a_min, a_max+1):
            j = multipliers[a % b]
            if j is None or a % 3 == 0:
                continue
            d = a**3 + norm_term
            r = ((d*j - a)//b) % d
            assert pow(r, 3, d) == K % d
            # Modulo nine each cube must be -1, so the signed pair sum is 1 mod 3.
            sign = 1 if d % 3 == 1 else -1
            first_t = (-sign*r) % d + FIRST_J*d
            divisors += 1
            live = (1 << WIDTH)-1
            for q, rows in tables[sign]:
                live &= rows[d % q][first_t % q]
                if not live:
                    break
            while live:
                lowest = live & -live
                step = lowest.bit_length()-1
                z = -sign*(first_t+step*d)
                exact += 1
                if show_survivors:
                    v = (4*((K-z**3)//(sign*d)) - d*d)//3
                    print("Survivor", sign*d, z, isqrt(v))
                xyz = recover(sign*d, z)
                if xyz is not None:
                    print('Solution', *xyz, flush=True)
                    solutions += 1
                live ^= lowest
    return divisors, divisors*WIDTH, exact, solutions


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--survivors", action="store_true")
    print('Pair sums, candidate coordinates, exact square tests, solutions')
    print(*search(show_survivors=parser.parse_args().survivors))
