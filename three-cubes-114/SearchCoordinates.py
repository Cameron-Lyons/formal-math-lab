"""Exhaust both signs of 10^19 < |z| <= 10^19 + 4096, for arbitrary x and y.

Run with: uv run --with python-flint==0.9.0 SearchCoordinates.py
"""

from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from math import isqrt, prod

from flint import fmpz


def allowed_coordinates(modulus):
    cubes = {v**3 % modulus for v in range(modulus)}
    sums = {(a + b) % modulus for a in cubes for b in cubes}
    return {v for v in range(modulus) if (114 - v**3) % modulus in sums}


ALLOWED = {m: allowed_coordinates(m) for m in (7, 9)}


def check_coordinate(z):
    if any(z % m not in allowed for m, allowed in ALLOWED.items()):
        return Counter(local=1), []
    n = 114 - z**3
    magnitude = abs(n)
    factors = fmpz(magnitude).factor()
    if prod(int(p) ** e for p, e in factors) != magnitude or not all(
        p.is_prime() for p, _ in factors
    ):
        raise ArithmeticError(f"Incomplete factorization for z = {z}")

    # A prime p = 2 mod 3 dividing x³+y³ must divide x+y. Multiplying
    # these distinct primes gives a mandatory divisor of the signed pair sum.
    forced = prod(int(p) for p, _ in factors if p % 3 == 2)
    counts = Counter(factored=1)
    if forced**3 > 4 * magnitude:
        counts["excluded_by_forced_product"] = 1

    # Independently visit ALL divisors, including those the forced-product
    # condition excludes. The actual search result does not rely on this filter.
    divisors = [1]
    for p, exponent in factors:
        divisors = [d * int(p) ** j for j in range(exponent + 1) for d in divisors]
    triples = []
    for d in divisors:
        # 4n = a³ + 3a(x-y)², with a = x+y. Thus a has the sign of n.
        if d**3 > 4 * magnitude:
            continue
        counts["bounded_divisors"] += 1
        a = d if n > 0 else -d
        delta = 4 * (magnitude // d) - d * d
        if delta % 3:
            continue
        diff = isqrt(delta // 3)
        if diff * diff * 3 == delta and (a + diff) % 2 == 0:
            x, y = (a + diff) // 2, (a - diff) // 2
            if x**3 + y**3 + z**3 != 114 or d % forced:
                raise ArithmeticError(f"Invalid reconstruction for z = {z}")
            triples.append((x, y, z))
    return counts, triples


def main():
    start = 10**19
    width = 4096
    coordinates = (sign * (start + i) for i in range(1, width + 1) for sign in (1, -1))
    total = Counter()
    solutions = 0
    with ProcessPoolExecutor(max_workers=3) as pool:
        for counts, triples in pool.map(check_coordinate, coordinates, chunksize=4):
            total.update(counts)
            for triple in triples:
                solutions += 1
                print("Solution", triple, flush=True)
    assert total["local"] + total["factored"] == 2 * width
    print(f"Coordinate magnitudes {start + 1} through {start + width}, both signs")
    print("Coordinates rejected modulo 7 or 9:", total["local"])
    print("Coordinates fully factored:", total["factored"])
    print(
        "Of those, excluded by the forced divisor alone:",
        total["excluded_by_forced_product"],
    )
    print("Divisors within the cube bound checked:", total["bounded_divisors"])
    print("Solutions:", solutions)


if __name__ == "__main__":
    main()
