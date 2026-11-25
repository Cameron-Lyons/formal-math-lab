"""Exact search for disjoint equal-LCM blocks of fixed length and large start.

Let X=2n+k+1, Y=2m+k+1, the doubled block centers. The centered product
P(X) = product(X+a) over a=1-k,3-k,...,k-1 is 2^k times the block product.
The binomial divisibilities proved in BinomialBounds.lean give
LCM(n,k) = k*choose(n+k,k)*t, where t divides lcm(1,...,k)/k.
Hence equal LCMs with X<Y imply P(Y)/P(X)=t_left/t_right>1.

For one such ratio r, write alpha=r^(1/k) and S=sum(a^2 for positive a).
F(X)=P(X)/X^k=product(1-a^2/X^2) lies in (0,1] and increases with X.
Then (Y/(alpha*X))^k=F(X)/F(Y) is at most 1 and at least F(X).
The bounds F(X)>=1-S/X^2 and z^(1/k)>=z for 0<=z<=1 give
0 <= alpha*X-Y <= alpha*S/X.

For an integer interval [lo,hi], certified endpoints A/Q <= alpha < (A+1)/Q
enclose every determinant d=q*Y-p*X in an explicit finite interval. For each
integer d in that interval, a modular inverse gives every possible X, and Y
is then forced. A continued-fraction convergent p/q of A/Q makes the interval
narrow. Completeness only requires gcd(p,q)=1 and the certified root bounds.
No step uses floating point. The last test compares exact integer block LCMs.
The optional coefficient sieve uses the valuation of t at each small prime,
which is periodic in the block start, and a slope bound that depends on r.
In this mode, product_matches counts exact product matches surviving both sieves.
"""

import argparse
from fractions import Fraction
from math import gcd, isqrt, lcm, prod


def floor_root(value, k):
    x = 1 << ((value.bit_length() + k - 1) // k)
    while True:
        next_x = ((k - 1) * x + value // x ** (k - 1)) // k
        if next_x >= x:
            return x
        x = next_x


def ratios(k):
    bound = lcm(*range(1, k + 1)) // k
    divisors = []
    for t in range(1, isqrt(bound) + 1):
        if bound % t == 0:
            divisors.append(t)
            if t * t != bound:
                divisors.append(bound // t)
    return sorted({Fraction(a, b) for a in divisors for b in divisors if a > b})


def convergents(a, q):
    p0, p1, q0, q1 = 0, 1, 1, 0
    while q:
        coefficient, r = divmod(a, q)
        p0, p1 = p1, coefficient * p1 + p0
        q0, q1 = q1, coefficient * q1 + q0
        yield p1, q1
        a, q = q, r


def ceil_div(a, b):
    return -((-a) // b)


def candidates(
    k,
    ratio,
    max_center,
    tight_bound=False,
    ratio_bound=False,
    progressions=((0, 1), (0, 1)),
):
    # A denominator above max_center^2 also keeps the root error well below 1/X.
    Q = 1 << (2 * max_center.bit_length())
    u, v = ratio.numerator, ratio.denominator
    target = u * Q**k
    A = floor_root(target // v, k)
    if not v * A**k <= target < v * (A + 1) ** k:
        raise ArithmeticError("incorrect root bounds")
    sum_squares = sum(a * a for a in range(k - 1, 0, -2))
    base_error = ceil_div((A + 1) * sum_squares, Q)

    (n_base, n_step), (m_base, m_step) = progressions
    x_base, y_base = 2 * n_base + k + 1, 2 * m_base + k + 1
    fractions = iter(convergents(A * n_step, Q * m_step))
    p, q = next(fractions)
    next_fraction = next(fractions, None)
    lo = k + 1
    while lo <= max_center:
        hi = min(2 * lo - 1, max_center)
        if (A + 1 - Q) * hi < 2 * k * Q:
            # Disjoint blocks need Y-X >= 2k, while Y <= alpha*X.
            lo = hi + 1
            continue
        error = base_error
        if (tight_bound or ratio_bound) and lo * lo > sum_squares:
            # For z=Y/(alpha*X), 1-z^k >= (1-z)*k*z^(k-1).
            # Since z^(k-1) >= z^k >= 1-S/X^2, this sharpens the coefficient
            # in alpha*X-Y <= error/X throughout this slab.
            error = min(
                error,
                ceil_div(
                    (A + 1) * sum_squares * lo * lo, Q * k * (lo * lo - sum_squares)
                ),
            )
            if ratio_bound:
                # If F(X)=prod(1-a^2/X^2), telescoping gives
                # F(Y)-F(X) <= S*(1/X^2-1/Y^2).
                # For z=Y/(alpha*X), F(Y)*z^(k-1)=F(X)/z >= F(X).
                # Therefore X*(alpha*X-Y) <= (alpha-1/alpha)*S/(k*F(X)).
                # A/Q <= alpha < (A+1)/Q and F(X) >= 1-S/lo^2.
                upper = A + 1
                error = min(
                    error,
                    ceil_div(
                        (upper * upper - Q * Q) * sum_squares * lo * lo,
                        upper * Q * k * (lo * lo - sum_squares),
                    ),
                )
        while next_fraction is not None and next_fraction[1] * n_step <= lo:
            p, q = next_fraction
            next_fraction = next(fractions, None)

        # X=x_base+2*n_step*i, Y=y_base+2*m_step*j. For h=q*j-p*i,
        # 2*n_step*m_step*h is
        #   (q*n_step*alpha-p*m_step)*X + p*m_step*x_base - q*n_step*y_base
        #   - q*n_step*(alpha*X-Y).
        left = q * n_step
        right = p * m_step
        lower_slope = left * A - right * Q
        upper_slope = lower_slope + left
        constant = (right * x_base - left * y_base) * Q
        min_term = min(lower_slope * lo, lower_slope * hi) + constant
        max_term = max(upper_slope * lo, upper_slope * hi) + constant
        denominator = 2 * n_step * m_step * Q
        first_h = ceil_div(min_term * lo - left * error * Q, denominator * lo)
        last_h = max_term // denominator
        i_lo = ceil_div(lo - x_base, 2 * n_step)
        i_hi = (hi - x_base) // (2 * n_step)
        if i_hi >= i_lo and last_h >= first_h:
            inverse = pow(p, -1, q)
            for h in range(first_h, last_h + 1):
                first_i = i_lo + (-h * inverse - i_lo) % q
                if first_i > i_hi:
                    continue
                j = (p * first_i + h) // q
                y = y_base + 2 * m_step * j
                for i in range(first_i, i_hi + 1, q):
                    x = x_base + 2 * n_step * i
                    if y >= x + 2 * k:
                        residual = A * x - Q * y
                        if -x <= residual and residual * x <= Q * error:
                            yield x, y
                    y += 2 * m_step * p
        lo = hi + 1


def coefficient_tables(k):
    # t(n)=(k-1)!*LCM(n,k)/prod(n+1,...,n+k). At q=p^a let
    # c=floor((n+k)/q)-floor(n/q). The product contributes c and
    # its LCM contributes 1 if c>0. For q>=k the difference vanishes.
    tables = []
    for p in range(2, k):
        if any(p % j == 0 for j in range(2, isqrt(p) + 1)):
            continue
        powers = [p]
        while powers[-1] * p < k:
            powers.append(powers[-1] * p)
        period = powers[-1]
        entries = []
        for n in range(period):
            e = sum((k - 1) // q - max(0, (n + k) // q - n // q - 1) for q in powers)
            entries.append(p**e)
        if max(entries) != min(entries):
            tables.append((period, entries))
    return tables


def coefficient_ratios(tables):
    # Each modulus is a power of a different prime. Its local exponents
    # determine that prime's contribution to t(n)/t(m). The Chinese
    # remainder theorem permits every combination of these residue classes.
    parts = [(1, 1)]
    for _, entries in tables:
        values = set(entries)
        local = {Fraction(a, b) for a in values for b in values}
        parts = [(u * r.numerator, v * r.denominator) for u, v in parts for r in local]
    return sorted(Fraction(u, v) for u, v in parts if u > v)


def residue_conditions(tables):
    # For each local multiplier ratio, collect all ordered residue pairs.
    # The gcd of all differences from the first admissible residue gives a
    # necessary congruence class for each start separately.
    conditions = []
    for period, entries in tables:
        pairs = {}
        for n, left in enumerate(entries):
            for m, right in enumerate(entries):
                pairs.setdefault(Fraction(left, right), []).append((n, m))
        local = {}
        for ratio, points in pairs.items():
            a, b = points[0]
            n_mod = gcd(period, *(n - a for n, _ in points))
            m_mod = gcd(period, *(m - b for _, m in points))
            local[(ratio.numerator, ratio.denominator)] = (
                (a % n_mod, n_mod),
                (b % m_mod, m_mod),
            )
        conditions.append((max(entries), local))
    return conditions


def combine_residues(first, second):
    a, modulus = first
    b, other = second
    if other == 1:
        return first
    t = (b - a) * pow(modulus, -1, other) % other
    return a + modulus * t, modulus * other


def start_progressions(ratio, conditions):
    left = right = (0, 1)
    for prime_power, local in conditions:
        key = gcd(ratio.numerator, prime_power), gcd(ratio.denominator, prime_power)
        first, second = local[key]
        left = combine_residues(left, first)
        right = combine_residues(right, second)
    return left, right


def multiplier_part(n, tables):
    return prod(entries[n % period] for period, entries in tables)


def search(k, max_start, bound_label=None, tight_bound=False, coefficient_sieve=False):
    tables = coefficient_tables(k) if coefficient_sieve else []
    rational_ratios = coefficient_ratios(tables) if coefficient_sieve else ratios(k)
    conditions = residue_conditions(tables)
    max_center = 2 * max_start + k + 1
    # A product of k consecutive integers is periodic modulo this modulus.
    # Only residue matches need the (potentially thousand-digit) exact products.
    modulus = 4093
    product_mod = [prod(range(n + 1, n + k + 1)) % modulus for n in range(modulus)]
    tested = product_matches = witnesses = 0
    for ratio in rational_ratios:
        starts = start_progressions(ratio, conditions)
        for x, y in candidates(
            k,
            ratio,
            max_center,
            tight_bound,
            ratio_bound=coefficient_sieve,
            progressions=starts,
        ):
            n, m = (x - k - 1) // 2, (y - k - 1) // 2
            tested += 1
            if (
                ratio.denominator * product_mod[m % modulus]
                - ratio.numerator * product_mod[n % modulus]
            ) % modulus:
                continue
            if coefficient_sieve and (
                ratio.denominator * multiplier_part(n, tables)
                != ratio.numerator * multiplier_part(m, tables)
            ):
                continue
            left, right = range(n + 1, n + k + 1), range(m + 1, m + k + 1)
            if ratio.denominator * prod(right) != ratio.numerator * prod(left):
                continue
            product_matches += 1
            if lcm(*left) == lcm(*right):
                witnesses += 1
                print(f"witness k={k} n={n} m={m}", flush=True)
    label = max_start if bound_label is None else bound_label
    print(
        f"k={k} n<={label} ratios={len(rational_ratios)} "
        f"candidates={tested} product_matches={product_matches} witnesses={witnesses}",
        flush=True,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    bounds = parser.add_mutually_exclusive_group()
    bounds.add_argument(
        "--max-start", type=int, help="largest earlier start parameter n"
    )
    bounds.add_argument(
        "--exponent",
        type=int,
        default=100,
        help="search through earlier start parameter n=10^E (default E=100)",
    )
    parser.add_argument(
        "--tight-bound",
        action="store_true",
        help="use the tighter error bound for faster searches at longer lengths",
    )
    parser.add_argument(
        "--coefficient-sieve",
        action="store_true",
        help="use exact periodic multipliers and a ratio-dependent slope bound",
    )
    parser.add_argument("lengths", type=int, nargs="*", default=[5, 6])
    args = parser.parse_args()
    if (
        args.exponent < 0
        or (args.max_start is not None and args.max_start < 0)
        or any(k < 1 for k in args.lengths)
    ):
        parser.error("expected a nonnegative maximum start and positive lengths")
    maximum = 10**args.exponent if args.max_start is None else args.max_start
    label = f"10^{args.exponent}" if args.max_start is None else str(maximum)
    for k in args.lengths:
        search(k, maximum, label, args.tight_bound, args.coefficient_sieve)
