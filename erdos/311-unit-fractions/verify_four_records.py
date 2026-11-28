"""Check the finite computations in four-records.md with integer and rational arithmetic."""

from fractions import Fraction
from itertools import product
from math import prod

# Each entry gives the coefficients of a linear form in x, y, z, w and its power.
FORMS = (
    ((0, 0, 0, 1), 4),
    ((0, 0, 1, -1), 4),
    ((0, 0, 1, 0), 7),
    ((0, 1, -1, -1), 2),
    ((0, 1, -1, 0), 6),
    ((0, 1, 0, -1), 2),
    ((0, 1, 0, 0), 6),
    ((0, 1, 1, -1), 2),
    ((1, -1, -1, 0), 1),
    ((1, -1, 0, 0), 4),
    ((1, -1, 1, 0), 1),
    ((1, 0, -1, 0), 3),
    ((1, 0, 0, 0), 3),
    ((1, 1, -1, 0), 3),
)
CASES = (
    ((2, 2, 2, 3), 1),
    ((2, 2, 2, 2), 3),
    ((1, 1, 1, 2), 13),
    ((1, 1, 1, 1), 19),
    ((0, 0, 0, 1), 34),
)


def check_forms():
    first_nonzero = [0] * 4
    for coefficients, power in FORMS:
        first = next(i for i, coefficient in enumerate(coefficients) if coefficient)
        first_nonzero[first] += power
    assert first_nonzero == [15, 18, 11, 4]
    assert sum(first_nonzero) == 48

    # A selected multiple jp of p contributes the integer label 6/j.
    labels = [{0}]
    for j in (1, 2, 3):
        previous = labels[-1]
        labels.append(previous | {s + 6 // j for s in previous})

    for caps, expected in CASES:
        pools = [labels[k] for k in caps]
        minimum = min(
            sum(
                power
                for coefficients, power in FORMS
                if sum(a * b for a, b in zip(coefficients, values, strict=True)) == 0
            )
            for values in product(*pools)
        )
        assert minimum == expected
        print(f"{caps}: {prod(map(len, pools))} tuples, minimum {minimum}")


def check_constant():
    def crossing(r):
        return 46 * r**3 + 169 * r**2 - 26 * r - 225

    # Check the polynomial identities at five points (degrees at most four).
    for r in range(5):
        numerator = 53 * r**2 + 61 * r
        denominator = 4 * r**3 + 11 * r**2 + 18 * r + 15
        assert (2 * r + 4) * numerator - 15 * denominator == crossing(r)
        derivative_numerator = (106 * r + 61) * denominator - numerator * (
            12 * r**2 + 22 * r + 18
        )
        assert (
            derivative_numerator
            == -212 * r**4 - 488 * r**3 + 283 * r**2 + 1590 * r + 915
        )

    # A lower bound for the derivative numerator on [1,9/8].
    upper = Fraction(9, 8)
    assert -212 * upper**4 - 488 * upper**3 + 283 + 1590 + 915 > 0
    assert crossing(1) < 0 < crossing(upper)
    r_low = Fraction("1.076013217211747")
    r_high = Fraction("1.076013217211749")
    assert crossing(r_low) < 0 < crossing(r_high)
    c_low = Fraction("0.812740330896927")
    c_high = Fraction("0.812740330896929")
    assert c_low < 5 / (2 * r_high + 4) < 5 / (2 * r_low + 4) < c_high
    assert 54 * c_high**2 + 73 * c_high < 95  # Below the three-record constant.
    print("0.812740330896927 < four-record constant < 0.812740330896929")


if __name__ == "__main__":
    check_forms()
    check_constant()
