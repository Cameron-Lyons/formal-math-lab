# Arbitrary-precision standard-monomial counter

`exact_standard_monomials.py` counts the finite staircase of a monomial ideal
using Python arbitrary-precision integers, without calling Singular's `vdim` or
`hilb` or using fixed-width integer accumulators.

To compute a polynomial quotient dimension, the input monomials **must** be the
leading monomials of a finished standard or Gröbner basis. Both the Python API
and the JSON CLI require `standard_basis_complete=True`. The counter cannot
check whether an exponent list actually came from a standard basis; the backend
that exports the leading ideal must verify completion first. Leading terms of a
partial basis or an arbitrary generating set must never be passed off as a
polynomial quotient dimension.

## Algorithm and correctness

A standard monomial is any exponent vector not coordinatewise greater than or
equal to any leading generator. A pure leading power `x_i^b_i` restricts that
variable's exponent to `0 <= a_i < b_i`. Having such a bound for every variable
is necessary and sufficient for a non-unit monomial ideal to have finite
staircase; the unit monomial immediately gives dimension 0.

The recursive counter works in four steps:

1. Tighten pure-power bounds, drop generators that cannot divide any monomial
   inside those bounds, and remove generators divisible by another generator,
   leaving a minimal antichain of forbidden corners.
2. Split generators into connected components on disjoint variable sets. Their
   staircase counts multiply, and unused variables simply contribute their
   bound sizes.
3. Pick a variable and split its exponent range at the generator thresholds.
   Inside each interval, the same subset of generators can divide a monomial.
   Projecting out that variable leaves a smaller subproblem whose count is
   multiplied by the interval length, summed over the disjoint intervals.
4. Memoize normalized states. Each recursive step removes a variable, and all
   arithmetic stays exact integer arithmetic.

Worst-case time is exponential. Callers can pass `max_states`; exceeding it
raises `CountLimitExceeded` with no partial count. Missing pure-power bounds
raise `MissingPurePowerBounds`. Exponent vectors are checked for uniform length
and nonnegative integers. Exporters must drop zero polynomials first, because
an all-zero exponent vector represents the leading monomial **1**, not zero.

## API and file contract

```python
from exact_standard_monomials import count_standard_monomials

stats = {}
dimension = count_standard_monomials(
    [[3, 0], [0, 4], [1, 2]],
    variables=2,
    standard_basis_complete=True,
    stats=stats,
    max_states=100000,
)
assert dimension == 8
```

The JSON format shared with the Singular backend is:

```json
{
  "format": "leading-monomial-ideal-v1",
  "variables": 2,
  "standard_basis_complete": true,
  "leading_monomials": [[3, 0], [0, 4], [1, 2]],
  "provenance": {"description": "completed and checked standard basis"}
}
```

Run `python experiments/exact_standard_monomials.py INPUT.json --output RESULT.json`.
The output saves `dimension_decimal` as a string so downstream JSON parsers do
not round large integers, along with the input SHA256, provenance, and
recursion stats.

## Independent checks

`exact_standard_monomials_check.py` passed 750 randomized tests against direct
finite-box enumeration, 10 fixed fixtures, 10 rejection tests, and 2 CLI/schema
checks. Each fixture is a monomial ideal, so its monomial generators are
already a standard basis.

Large arithmetic and structural fixtures include:

- Pure-cubic ideal in 100 variables:
  `3^100 = 515377520732011331036461129765621272702107522001`, in 1 state.
- Pure-tenth-power ideal in 20 variables:
  `10^20 = 100000000000000000000`.
- Pure-cubic ideal plus the product of all 100 variables: `3^100 - 2^100`, in
  199 states.
- Binary bounds with adjacent-pair generators along a 100-variable path:
  `Fibonacci(102) = 927372692193078999176`, in 197 states with 96 cache hits
  and 96 component factorizations.
- Two bounds of `10^80` plus generator `xy`: `2*10^80-1`, counted directly via
  intervals without looping across `10^80`.

These test the counter's arithmetic and algorithm only; **they are not the
ternary T-board count**. This module has not computed any T-board ideal count.
Results are saved in `exact_standard_monomials_check_results.json` and can be
reproduced with `python experiments/exact_standard_monomials_check.py`.
