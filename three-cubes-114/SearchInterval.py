# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.9.0"]
# ///
"""Run `uv run SearchInterval.py` to repeat the contiguous pair-sum search."""

from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from math import gcd, isqrt, prod

from flint import fmpz, fmpz_mod_poly_ctx


D_START = 2 * 10**17
D_COUNT = 10_000_000
Z_MAX = 10**20
SQUARES_19 = frozenset(x * x % 19 for x in range(19))


@lru_cache(maxsize=32768)
def prime_power_roots(p, e):
    """Find all roots of z^3 = 114 modulo p^e."""
    assert fmpz(p).is_prime()
    if 114 % p == 0:
        # 114 is squarefree. A multiple of p cubed cannot equal 114 mod p^2.
        return (0,) if e == 1 else ()
    if p % 3 == 2:
        roots = [pow(114, (2 * p - 1) // 3, p)]
    elif pow(114, (p - 1) // 3, p) != 1:
        return ()
    else:
        polynomial = fmpz_mod_poly_ctx(p)([-114, 0, 0, 1])
        roots = [int(r) for r in polynomial.roots(multiplicities=False)]
        # A nonzero cube has exactly three roots for these primes.
        assert len(set(roots)) == len(roots) == 3

    # Each root is simple, so it has exactly one lift at every higher power.
    modulus = p
    for _ in range(1, e):
        for i, r in enumerate(roots):
            correction = ((114 - r**3) // modulus) * pow(3 * r * r, -1, p)
            roots[i] = r + modulus * (correction % p)
        modulus *= p
    assert all((r**3 - 114) % modulus == 0 for r in roots)
    return tuple(roots)


def cube_roots(d):
    """Combine the prime-power roots by the Chinese remainder theorem."""
    factors = [(int(p), e) for p, e in fmpz(d).factor()]
    assert prod(p**e for p, e in factors) == d
    roots, modulus = [0], 1
    for p, e in factors:
        local = prime_power_roots(p, e)
        if not local:
            return []
        q = p**e
        inverse = pow(modulus, -1, q)
        roots = [a + modulus * ((b - a) * inverse % q) for a in roots for b in local]
        modulus *= q
    return roots


def search_block(bounds):
    start, stop, z_max = bounds
    counts = Counter()
    for d in range(start, stop):
        counts['pair sums'] += 1
        # Cubes mod 9 force x,y,z = -1 mod 3, so signed D=x+y is 1 mod 3.
        if d % 3 == 0:
            continue
        D = d if d % 3 == 1 else -d
        # For even D, z is even and x,y must be odd, giving D = 114 mod 8.
        if D % 2 == 0 and D % 8 != 2:
            continue
        # For 19 | D, write D=19e. Dividing the equation by 19 gives
        # e*x^2 = 2 mod 19, so e is a nonzero nonsquare.
        if D % 19 == 0 and (D // 19) % 19 in SQUARES_19:
            continue
        roots = cube_roots(d)
        if not roots:
            continue
        counts['pair sums with progressions'] += 1

        # 114-z^3 = D*(x^2-xy+y^2); the factor multiplying D is positive.
        low, high = (-z_max, min(4, z_max)) if D > 0 else (5, z_max)
        # For x=3a-1, x^3=9a-1 mod 27. Hence x+y+z is zero mod 9,
        # and is even by parity. Combine z=-D mod 18 with each root mod d.
        g = gcd(d, 18)
        lift = 18 // g
        inverse = pow(d // g, -1, lift)
        stride = d * lift
        for r in roots:
            assert (-D - r) % g == 0
            r += d * (((-D - r) // g) * inverse % lift)
            counts['progressions'] += 1
            first = low + (r - low) % stride
            counts['candidate z values'] += max(0, 1 + (high - first) // stride)
            for z in range(first, high + 1, stride):
                # 3*(x-y)^2 = 4*(114-z^3)/D - D^2. Since z^3 = 114
                # mod d, the division here is exact for either sign of D.
                disc = 4 * ((114 - z**3) // D) - d * d
                if disc < 0 or disc % 3:
                    continue
                difference = isqrt(disc // 3)
                if difference**2 * 3 == disc and (D + difference) % 2 == 0:
                    x, y = (D + difference) // 2, (D - difference) // 2
                    assert x**3 + y**3 + z**3 == 114
                    print('Solution', x, y, z, flush=True)
                    counts['solutions'] += 1
    return counts


if __name__ == '__main__':
    stop = D_START + D_COUNT
    print(f'Searching {D_START} <= |x+y| < {stop}, |z| <= {Z_MAX}', flush=True)
    block_size = 100_000
    blocks = [(d, min(d + block_size, stop), Z_MAX) for d in range(D_START, stop, block_size)]
    counts = Counter()
    with ProcessPoolExecutor(max_workers=4) as pool:
        for result in pool.map(search_block, blocks):
            counts.update(result)
    assert counts['pair sums'] == D_COUNT
    for key in ['pair sums', 'pair sums with progressions', 'progressions', 'candidate z values', 'solutions']:
        print(key, counts[key])
