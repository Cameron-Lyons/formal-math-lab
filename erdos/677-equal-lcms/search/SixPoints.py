"""Enumerate every integral b with F(b)=r*F(a) for |a| bounded and F(t)=t(t-1)(t-3).

For a>=4, b>a necessarily. For a<=-1, b<a necessarily. Set s=1 or -1
respectively, X=s*(3a-4), Y=s*(3b-4). Then Y>X>=7 and
P_s(Y)=r*P_s(X), where P_s(X)=X^3-21X-20s. The remaining a=0,1,2,3
are handled directly. In particular a=2 would require F(b)=-4,-5,-10,-20,
which lie outside the integer image (F(-2)=-30, F(-1)=-8; and F(2)=-2).

P_s(t)/t^3 is positive, at most 1, and increasing for t>=7 (its derivative
is (42t+60s)/t^4). Thus for alpha=r^(1/3), z=Y/(alpha X) satisfies
1-24/X^2 <= z^3 <= 1. Using 1+z+z^2>=3z^3, one obtains
0 <= alpha*X-Y <= 24*alpha/(3*X*(1-24/X^2)).

For lo<=X<=hi, exact root bounds A/Q <= alpha < (A+1)/Q and a rational
convergent p/q bound the integer d=qY-pX. Each possible d gives a single
residue class for X modulo q. The loop enumerates that entire class and
checks the cubic equation exactly. There is no upper bound imposed on b.
"""

import argparse

from height import ceil_div, convergents, floor_root

RATIOS = [(2, 1), (5, 2), (5, 1), (10, 1)]


def cubic(t):
    return t * (t - 1) * (t - 3)


def affine_points(u, v, bound):
    zeros = [0, 1, 3]
    points = {(a, b) for a in zeros if a <= bound for b in zeros}
    max_center = 3 * bound + 4
    Q = 1 << (2 * max_center.bit_length())
    target = u * Q**3
    A = floor_root(target // v, 3)
    if not v * A**3 <= target < v * (A + 1) ** 3:
        raise ArithmeticError("inexact root enclosure")

    modulus = 4093
    values = [cubic(i) % modulus for i in range(modulus)]
    fractions = iter(convergents(A, Q))
    p, q = next(fractions)
    inverse = 0  # The first convergent has denominator one.
    next_fraction = next(fractions, None)
    det_sign = -1  # p_next*q - p*q_next
    candidates = 0
    lo = 7
    while lo <= max_center:
        hi = min(2 * lo - 1, max_center)
        while next_fraction is not None and next_fraction[1] <= lo:
            previous_q = q
            p, q = next_fraction
            # Consecutive convergents have determinant alternating +1, -1,
            # starting with p_1*q_0 - p_0*q_1 = +1.
            det_sign = -det_sign
            inverse = (det_sign * previous_q) % q
            next_fraction = next(fractions, None)
        if (p * inverse) % q != 1 % q:
            raise ArithmeticError("incorrect inverse")

        error = ceil_div(24 * (A + 1) * lo**2, 3 * Q * (lo**2 - 24))
        left = q * A - p * Q
        right = left + q
        min_term = min(left * lo, left * hi)
        max_term = max(right * lo, right * hi)
        low_d = ceil_div(min_term * lo - q * error * Q, Q * lo)
        high_d = max_term // Q
        for d in range(low_d, high_d + 1):
            x = lo + (-d * inverse - lo) % q
            while x <= hi:
                residue = x % 3
                if residue:
                    y = (p * x + d) // q
                    if y > x and y % 3 == residue:
                        sign = 1 if residue == 2 else -1
                        a = (4 + sign * x) // 3
                        b = (4 + sign * y) // 3
                        if abs(a) <= bound:
                            candidates += 1
                            if (
                                v * values[b % modulus] - u * values[a % modulus]
                            ) % modulus == 0 and v * cubic(b) == u * cubic(a):
                                points.add((a, b))
                x += q
        lo = hi + 1
    return sorted(points), candidates


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--exponent", type=int, default=100, help="search |a| <= 10^E")
    args = parser.parse_args()
    if args.exponent < 0:
        parser.error("expected a nonnegative exponent")
    for u, v in RATIOS:
        found, tested = affine_points(u, v, 10**args.exponent)
        print(
            f"r={u}/{v} |a|<=10^{args.exponent} candidates={tested} points={found}",
            flush=True,
        )
