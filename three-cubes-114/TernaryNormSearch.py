"""Search CRT-joined roots from primitive ternary norms. Run with Python 3.9+.

For target 114 the coefficient box is inclusive in all three dimensions.
We keep g > 1, gcd(g,d) = 1, 3 ∤ M and 54M > 10^19. For each distinct
(M,r), we test the root class with 3M ≤ |z| < 51M. A second run searches
the next 10,000 values of a using only M that are noncubes modulo 19.
The sign of z is opposite to x+y throughout both boxes. All arithmetic is exact.
"""

from collections import Counter
from math import gcd

from NormSearch import MODULI, WIDTH, K, masks, recover

A_MIN, A_MAX = 3_000_000, 3_009_999
B_MAX, C_MAX = 40, 40
CUBES_19 = frozenset(pow(t, 3, 19) for t in range(19))


def prime_divisors(n):
    """Distinct positive prime divisors of a nonzero integer."""
    n = abs(n)
    p = 2
    while p * p <= n:
        if n % p == 0:
            yield p
            while n % p == 0:
                n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        yield n


def row_candidates(k, b, c, lo, hi):
    # For coprime b,c, g = gcd(b²-ac, b³-kc³). Indeed c is invertible
    # modulo the latter gcd, and the two relations force g | A and g | B.
    candidates = set()
    for p in prime_divisors(b**3 - k * c**3):
        first = lo + (b * b * pow(c, -1, p) - lo) % p
        candidates.update(range(first, hi + 1, p))
    return candidates


def joined_root(k, a, b, c):
    """Return (g,d,M,r), with M=gd, if the two moduli are coprime."""
    n = a**3 + k * b**3 + k * k * c**3 - 3 * k * a * b * c
    A, B, C = a * a - k * b * c, k * c * c - a * b, b * b - a * c
    g = gcd(A, B, C)
    d, rem = divmod(abs(n), g * g)
    assert rem == 0 and gcd(a, b, c) == 1
    if gcd(g, d) != 1:
        return None
    u = b * pow(c, -1, g) % g
    v = (B // g) * pow(C // g, -1, d) % d
    m = g * d
    r = v + d * ((u - v) * pow(d, -1, g) % g)
    assert (r**3 - k) % m == 0
    return g, d, m, r


def bit_tables(k):
    return {s: [(q, masks(q, s, k)) for q in MODULI] for s in (-1, 1)}


def scan_root(k, m, r, first_band, band_width, tables):
    """Count exact-square tests and return all triples in the given |z|/m band."""
    assert k % 9 in (3, 6) and m % 3 and 1 <= band_width <= WIDTH
    # For k=3ε mod 9 the three coordinates equal ε mod 3. Thus x+y=-ε mod 3.
    signed_class = 2 if k % 9 == 3 else 1
    sign = 1 if m % 3 == signed_class else -1
    first_t = first_band * m + ((-sign * r) % m)
    live = (1 << band_width) - 1
    for q, rows in tables[sign]:
        live &= rows[m % q][first_t % q]
        if not live:
            return 0, []
    hits = []
    checked = 0
    while live:
        bit = live & -live
        checked += 1
        z = -sign * (first_t + (bit.bit_length() - 1) * m)
        xyz = recover(sign * m, z, k)
        if xyz is not None:
            hits.append(xyz)
        live ^= bit
    return checked, hits


def controls():
    assert joined_root(114, 1, 4, 1) == (5, 757, 3785, 1269)
    # Grantham–Walsh §2: this root and quotient lead to the known k=3 triple.
    g, d, m, r = joined_root(3, 5603, 1612, 1156)
    assert (g, d, m, r) == (1, 108398887211, 108398887211, 21397363547)
    xyz = (569936821221962380720, -569936821113563493509, -472715493453327032)
    _, hits = scan_root(3, m, r, abs(xyz[2]) // m, 1, bit_tables(3))
    assert hits == [xyz]


def search(a_min=A_MIN, a_max=A_MAX, only_noncubes=False):
    tables = bit_tables(K)
    counts = Counter()
    seen = set()
    print(
        f"a = {a_min} through {a_max} (noncube moduli only = {only_noncubes})",
        flush=True,
    )
    for b in range(1, B_MAX + 1):
        for c in range(1, C_MAX + 1):
            if gcd(b, c) != 1:
                continue
            counts["coefficient triples"] += a_max - a_min + 1
            for a in row_candidates(K, b, c, a_min, a_max):
                counts["generators with g > 1"] += 1
                result = joined_root(K, a, b, c)
                if result is None:
                    continue
                g, _d, m, r = result
                assert g > 1
                if m % 3 == 0 or 54 * m <= 10**19:
                    continue
                counts["eligible generators before modulo-19 restriction"] += 1
                # Every absolute full norm is a cube modulo 19. An M in the
                # complementary classes is accessible here by dividing N by g.
                noncube = m % 19 not in CUBES_19
                if only_noncubes and not noncube:
                    continue
                if (m, r) in seen:
                    continue
                seen.add((m, r))
                if noncube:
                    counts["distinct progressions with noncube M modulo 19"] += 1
                checked, hits = scan_root(K, m, r, 3, 48, tables)
                counts["square tests after masks"] += checked
                for xyz in hits:
                    print("Solution", *xyz, flush=True)
                    counts["solutions"] += 1
    counts["distinct joined progressions"] = len(seen)
    counts["candidate coordinates"] = len(seen) * 48
    for key in (
        "coefficient triples",
        "generators with g > 1",
        "eligible generators before modulo-19 restriction",
        "distinct joined progressions",
        "distinct progressions with noncube M modulo 19",
        "candidate coordinates",
        "square tests after masks",
        "solutions",
    ):
        print(key, counts[key])
    return counts


if __name__ == "__main__":
    controls()
    print(
        "Modulus 3785 and the Grantham–Walsh k=3 positive control passed.", flush=True
    )
    search()
    search(A_MAX + 1, A_MAX + 10_000, only_noncubes=True)
