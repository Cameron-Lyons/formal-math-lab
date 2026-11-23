"""Extend the endpoint search in search.cpp to a bound on m - n.

Suppose two disjoint blocks of length k and displacement d have common LCM H.
Every prime power dividing H must divide some entry in each block. It then
divides their positive difference in [d-k+1, d+k-1]. Consequently H divides
the LCM of this length-(2k-1) interval.

For a length-r interval ending at b with LCM L, we have

    r * binom(b, r) <= L <= lcm(1,...,r) * binom(b, r).

Indeed, in the interval product divided by L, the contribution to the
p-adic valuation at each level q=p^a equals max(0, count_multiples(q)-1).
It is at most floor((r-1)/q) and at least max(0, floor(r/q)-1). Summing over
a shows the product divided by L divides (r-1)! and is a multiple of
r!/lcm(1,...,r), proving the two bounds.

For a hypothetical solution whose later endpoint exceeds B and d <= D,
use these bounds on the later block and on the interval of differences:

    k * binom(B+1, k) <= H <= lcm(1,...,2k-1) * binom(D+k-1, 2k-1).

This script checks that the inequalities are incompatible for every k <= D.
Together with a negative search.cpp run through B, this covers every d <= D
with unrestricted endpoints. All binomial updates use exact integer arithmetic.
"""

from math import lcm


def verify(endpoint: int, displacement: int) -> None:
    assert 1 <= displacement <= endpoint
    later_binomial = endpoint + 1
    difference_binomial = displacement
    small_lcm = 1
    for k in range(1, displacement + 1):
        small_lcm = lcm(small_lcm, 2 * k - 1)
        if k * later_binomial <= small_lcm * difference_binomial:
            raise ValueError(f"bounds insufficient at length {k}")
        later_binomial = later_binomial * (endpoint + 1 - k) // (k + 1)
        difference_binomial = (
            difference_binomial * (displacement + k) * (displacement - k)
            // (2 * k * (2 * k + 1))
        )
        small_lcm = lcm(small_lcm, 2 * k)
    print(f"excluded all endpoints > {endpoint} for every displacement <= {displacement}")


if __name__ == "__main__":
    verify(10_000_000, 7_000)
