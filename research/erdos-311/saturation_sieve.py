"""Certify L_n * delta(n) > n^5 for every n from 1,000 to 1,000,000."""

from bisect import bisect_right
from math import isqrt, lcm, prod


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            count = (limit - p * p) // p + 1
            sieve[p * p :: p] = bytes(count)
    return [p for p, present in enumerate(sieve) if present]


def lcm_changes(primes: list[int], limit: int) -> tuple[list[int], list[int]]:
    # At a prime power p^j, and only there, L_n / L_(n-1) equals p.
    events = []
    for p in primes:
        power = p
        while power <= limit:
            events.append((power, p))
            power *= p
    events.sort()
    return [n for n, _ in events], [p for _, p in events]


def nonempty_weights(test_primes: list[int], modulus: int) -> list[int]:
    # Choosing prime p contributes L_n/p = (L_n/P) * (P/p).
    weights: list[int] = [0]
    for p in test_primes:
        term = modulus // p
        weights.extend([w + term for w in weights])
    return weights[1:]


def check_segment(end: int, factor: int, modulus: int, weights: list[int]) -> None:
    # Along this segment the numerator restrictions are constant, and n^5
    # is largest at the final n. The empty mask requires a nonzero multiple of P.
    bound = end**5
    if modulus <= bound:
        raise ValueError(f"test modulus too small at {end}")
    for w in weights:
        residue = factor * w % modulus
        if min(residue, modulus - residue) <= bound:
            raise ValueError(f"test primes leave a candidate at segment ending {end}")


def check_range(first: int, last: int) -> tuple[int, int]:
    primes = primes_through(last)
    levels, multipliers = lcm_changes(primes, last)
    start = first
    blocks = segments = 0
    while start <= last:
        end = min(3 * start // 2, last)
        limit = bisect_right(primes, start)
        test_primes = primes[max(0, limit - 7) : limit]
        if len(test_primes) != 7 or 2 * min(test_primes) <= end:
            raise ValueError(f"need seven primes between {end}/2 and {start}")
        modulus = prod(test_primes)
        selected = set(test_primes)
        weights = nonempty_weights(test_primes, modulus)
        event = bisect_right(levels, start)
        first_event = event
        factor = 1
        for j in range(event):
            if levels[j] not in selected:
                factor = factor * multipliers[j] % modulus
        if start == first:
            # Cross-check the initial residue against the defining integer LCM.
            direct = lcm(*range(1, start + 1)) // modulus
            if direct % modulus != factor:
                raise ValueError("LCM initialization failed")
        while event < len(levels) and levels[event] <= end:
            check_segment(levels[event] - 1, factor, modulus, weights)
            factor = factor * multipliers[event] % modulus
            event += 1
        check_segment(end, factor, modulus, weights)
        blocks += 1
        segments += 1 + event - first_event
        start = end + 1
    return blocks, segments


if __name__ == "__main__":
    beginning, ending = 1_000, 1_000_000
    block_count, segment_count = check_range(beginning, ending)
    print(
        f"Verified L_n * delta(n) > n^5 for {beginning} <= n <= {ending} "
        f"({ending - beginning + 1} indices, {block_count} blocks, "
        f"{segment_count} constant-LCM segments)."
    )
