"""Exact search for signed pair sums x+y = -19p in a thin slice beyond 10^19/54.

Run with Python 3.8 or later. The only dependency is the standard library.
"""

from itertools import compress
from math import isqrt


P_START = 10**16
P_STOP = P_START + 10**6  # exclusive
Z_MAX = 10**21


def primes_in_interval(start, stop):
    """Yield every prime in [start, stop), for 2 <= start < stop."""
    limit = isqrt(stop - 1)
    # Index i represents the odd number 2i+1. Sieve all possible prime factors.
    odd_primes = bytearray([1]) * ((limit + 1) // 2)
    odd_primes[0] = 0
    for p in range(3, isqrt(limit) + 1, 2):
        if odd_primes[p // 2]:
            first = (p * p) // 2
            count = 1 + (len(odd_primes) - 1 - first) // p
            odd_primes[first::p] = bytes(count)

    prime = bytearray([1]) * (stop - start)
    for p in compress(range(1, limit + 1, 2), odd_primes):
        first = max(p * p - start, (-start) % p)
        if first < len(prime):
            count = 1 + (len(prime) - 1 - first) // p
            prime[first::p] = bytes(count)

    if start <= 2 < stop:
        yield 2
    for p in range(max(3, start | 1), stop, 2):
        if prime[p - start]:
            yield p


def search():
    squares19 = {x * x % 19 for x in range(1, 19)}
    pair_sums = rejected_sums = baseline = skipped = tested = solutions = 0
    for p in primes_in_interval(P_START, P_STOP):
        if p % 3 != 2:
            continue
        d = 19 * p
        # All coordinates are -1 mod 3, so x+y is 1 mod 3. Here d is 2
        # mod 3 and the signed sum must be -d. Consequently z^3 >= 114.
        pair_sums += 1

        # The unique cube root of 114 mod p (3 is invertible mod p-1).
        root_p = pow(114, (2 * p - 1) // 3, p)
        # Combine z = root_p mod p and z = 0 mod 19 to get z mod d.
        root = 19 * (root_p * pow(19, -1, p) % p)
        # Writing each coordinate as 3a-1 gives (3a-1)^3 = 9a-1 mod 27.
        # Thus a+b+c = 1 mod 3 and x+y+z = 0 mod 9. It is also even,
        # since cubes preserve parity. This gives z = d mod 18.
        root += d * ((d - root) * pow(d, -1, 18) % 18)
        stride = 18 * d
        count = max(0, 1 + (Z_MAX - root) // stride)
        baseline += count

        # For x+y=19e, the cube equation gives e*x^2 = 2 mod 19.
        # Here e=-p and 2 is a nonsquare, so -p cannot be a square.
        # We computed the root above even for rejected d to count the skips.
        if (-p) % 19 in squares19:
            rejected_sums += 1
            skipped += count
            continue

        for z in range(root, Z_MAX + 1, stride):
            tested += 1
            # From x^2-xy+y^2=(z^3-114)/d and x+y=-d,
            # 3(x-y)^2 = 4(z^3-114)/d - d^2.
            quotient = (z**3 - 114) // d
            disc = 4 * quotient - d * d
            if disc < 0 or disc % 3:
                continue
            diff = isqrt(disc // 3)
            if 3 * diff * diff == disc and (diff - d) % 2 == 0:
                x, y = (-d + diff) // 2, (-d - diff) // 2
                assert x**3 + y**3 + z**3 == 114
                print("Solution", x, y, z)
                solutions += 1

    assert baseline == skipped + tested
    print("Pair sums considered:", pair_sums)
    print("Pair sums rejected by the modulo-19 test:", rejected_sums)
    print("Values of z in the baseline progressions:", baseline)
    print("Values of z skipped by the modulo-19 test:", skipped)
    print("Values of z tested exactly:", tested)
    print("Solutions found:", solutions)


if __name__ == "__main__":
    search()
