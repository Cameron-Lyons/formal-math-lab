# Arbitrary-precision standard-monomial counter

`exact_standard_monomials.py` counts the finite staircase of a monomial ideal
using Python integers. It does not call Singular's `vdim` or `hilb` and does
not use a machine-sized count accumulator.

For a polynomial quotient, the supplied monomials **must** be the leading
monomials of a completed standard/Gröbner basis. The API requires the explicit
attestation `standard_basis_complete=True`, and the JSON frontend requires
that same Boolean field. The counter cannot independently certify a standard
basis from exponent vectors alone. The exporting backend is responsible for
completing and validating that computation. A partial basis or the leading
terms of arbitrary polynomial generators must not be used to claim a
polynomial quotient dimension.

## Algorithm and correctness

A standard monomial has an exponent vector that is not coordinatewise above
any leading generator. A pure leading power `x_i^b_i` bounds its exponent by
`0 <= a_i < b_i`. Such a bound for every variable is necessary and sufficient
for finiteness of a non-unit monomial ideal. The unit monomial instead yields
dimension zero immediately.

The recursive counter:

1. Tightens pure-power bounds, drops generators that cannot divide any
   monomial within the bounds, and removes generators divisible by another
   generator. This leaves a minimal antichain of forbidden exponent regions.
2. Factors components whose generator supports use disjoint variable sets.
   Their staircase sizes multiply; unused variables contribute their bounds.
3. Chooses a variable and partitions its bounded exponent range at generator
   thresholds. Within an interval, the same generators can divide a monomial.
   Removing this coordinate gives a smaller counting problem, whose count is
   multiplied by the interval length. The intervals are disjoint and exhaustive.
4. Memoizes normalized states. Every recursive branch reduces the variable
   set, and all arithmetic remains integral and exact.

The method has exponential worst-case complexity. A caller can set a
canonical-state limit; reaching it raises `CountLimitExceeded` and produces
no partial numerical answer. Missing pure-power bounds raise
`MissingPurePowerBounds`. Exponent vectors are checked for length and
nonnegative integer entries. Zero polynomials must be removed by the exporter:
an all-zero exponent vector means the leading monomial **1**, not a zero
polynomial.

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

The file schema agreed with the Singular backend is:

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
The output stores `dimension_decimal` as a string, preventing a downstream JSON
consumer from rounding integers larger than its numeric type supports. It also
retains the input SHA256, provenance, and recursion statistics.

## Independent checks

`exact_standard_monomials_check.py` passed 750 randomized comparisons with
direct finite-box enumeration, ten fixed fixtures, ten rejection tests, and
two CLI/schema checks. The fixtures themselves are monomial ideals, for which
the monomial generators are a standard basis automatically.

Large arithmetic and structural checks include:

- The pure-cubic ideal in 100 variables: exactly
  `3^100 = 515377520732011331036461129765621272702107522001`, counted in one state.
- The pure-tenth-power ideal in 20 variables: exactly
  `10^20 = 100000000000000000000`.
- The pure-cubic ideal plus the product of all 100 variables: exactly
  `3^100 - 2^100`, counted in 199 states.
- Binary bounds with adjacent-pair generators along a 100-variable path:
  `Fibonacci(102) = 927372692193078999176`, counted in 197 states with 96 cache
  hits and 96 component factorizations.
- Two bounds of `10^80` and generator `xy`: exactly `2*10^80-1`, without
  iterating through that exponent range.

These are arithmetic and algorithm fixtures, **not the ternary T-board count**.
No count of the T-board polynomial ideal has been computed by this module.
Results are retained in `exact_standard_monomials_check_results.json`; reproduce
them with `python experiments/exact_standard_monomials_check.py`.
