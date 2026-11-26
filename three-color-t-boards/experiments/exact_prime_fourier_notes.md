# Fourier ideals in odd prime characteristic

`exact_prime_fourier.py` builds all 81 T placements directly from row and
column geometry. It imports no characteristic-two polynomial lists and never
reuses coefficients that were reduced modulo 2. It accepts any small prime `p`
congruent to 2 modulo 3 (with exact primality checking); the tested primes are
**5, 29, and 83**.

## Field, equations, and exact count

Use ordinary polynomial variables with cubic domains `z_i^3-1=0`. Because 3
does not divide `p-1`, `F_p` contains no nontrivial cube root of unity, so
`a^2+a+1` is irreducible over `F_p`. In the quadratic extension `F_(p^2)`, the
three distinct cube roots are

```text
color 0 -> 1       color 1 -> a       color 2 -> -1-a.
```

For each role-exponent vector `e` in `{0,1,2}^4`, define the moment
`P_e = sum_over_placements product_over_roles z_cell^e_role`. All nonconstant
moments must vanish. The zeroth moment equals `81 mod p` automatically; it is
not set to zero or replaced by 1 in odd characteristic.

The 81-character Fourier transform on the 81 patterns is invertible, since it
is the fourth tensor power of the invertible 3-by-3 Vandermonde matrix on the
three cube roots. The all-ones pattern-count vector has zeroth transform 81 and
all other transforms 0. Setting all nonconstant moments to zero therefore
forces every integer pattern count to satisfy `n_s == 1 (mod p)`. Since every
count is nonnegative, each is at least 1, and summing to 81 forces all 81 counts
to equal 1. For every allowed prime, the solutions are exactly the valid boards.

Because `p == 2 mod 3`, Frobenius gives `P_e^p = P_(2e mod 3)` modulo the cubic
domains. By default, the exporter keeps the **40** vectors whose first nonzero
entry is 1, picking one from each nonconstant Frobenius pair. This still works
with a fixed prefix because Frobenius also conjugates the prefix coefficients.

Passing `all_moments=True` exports **all 80** nonconstant moments. The 40
default equations stay unchanged, and metadata marks the other 40 as redundant.
Including them explicitly may help a standard-basis solver avoid deriving them
via `p`th powers and domain reductions, without changing the ideal.

Because `p != 3`, the cubic domains are separable. Extending scalars to
`F_(p^2)` splits their quotient into a product of fields, one per labeled
coloring, and adding the moments keeps exactly the valid-board factors with
multiplicity 1. The ordinary `F_p` quotient dimension of the full model is
therefore already the full labeled board count (**multiplier 1**). Prefix
models with quadratic coefficients work over `F_(p^2)` and count extensions of
that fixed prefix. No Boolean relations, color normalization, or reflection
normalization are added.

## Why 29 already gives exact low-order margins

If every moment supported on a set of `k` roles vanishes, Fourier inversion
forces each of its `3^k` marginal counts to equal `3^(4-k) (mod p)`. Whenever
`p > 3^(4-k)`, every nonnegative count is at least `3^(4-k)`, and summing to 81
forces equality everywhere:

| Marginal order | Exact target per category | Sufficient prime threshold |
| --- | ---: | ---: |
| One role | 27 | `p > 27` |
| Two roles | 9 | `p > 9` |
| Three roles | 3 | `p > 3` |
| Four roles | 1 | `p > 1` |

Both 29 and 83 enforce exact one-role margins at the same linear moment layer,
and 29 is the smallest prime congruent to 2 modulo 3 above 27. There is no
reason here to expect stronger marginal pruning from 83. Prime 5 forces exact
three-role margins on its own, though not exact one-role or two-role margins at
lower layers.

## API and coefficient handling

```python
from exact_prime_fourier import generate_model

full = generate_model(29)
full80 = generate_model(29, all_moments=True)
prefix = generate_model(29, prefix_rows, all_moments=True)
```

The schema records `coefficient_characteristic`, `variables`,
`free_original_cells`, explicit cubic `domain_equations`, and
`moment_equations`. Each term looks like:

```json
{"coefficient": [2, 28], "monomial": [[0, 1], [4, 2]]}
```

Here `[u, v]` stands for `u + v*a`, and variable indices point into the 0-based
free-variable list. Fixed-prefix colors are substituted before collecting
terms. For each monomial, the generator first records its **integer**
multiplicities `n0, n1, n2` at the three cube roots in
`integer_occurrence_groups`, then reduces to `[(n0-n2) mod p, (n1-n2) mod p]`
so cancellation depends only on the chosen prime. Every generated model keeps
`standard_basis_complete=False`.

The algebra backend loads this format as `prime:29` (40 equations) or
`prime-all:29` (80 equations), using ordinary `F29` when all coefficients lie
in the prime field and the quadratic extension with `a^2+a+1` when a fixed
prefix introduces extension coefficients.

## Verification and full-import audit

For **each** of 5, 29, and 83, the test suite passed:

- 2,400 comparisons of exported equations against a direct Fourier transform of
  integer pattern counts on random boards, across prefix lengths 0, 1, 6, 9,
  and 10.
- 2,400 checks of explicit Frobenius partners against the representative's
  `p`th power, plus exact equality of the default 40 equations to the matching
  subset of all 80.
- All 80 equations on **1,557 distinct valid witness boards**, deduplicated
  from the published seeds, `extended_seeds.json`, and the gauge certificate.
- Five fully fixed valid boards, each giving the zero ideal in zero free
  variables, plus rejection of the uniform-triple counterexample by 8
  representative equations (and all 16 matching all-80 equations).
- Tiny exhaustive root fixtures: 9 ordered pairs of cube roots and 6 ordered
  triples satisfying `x+y+z=0`.

Check outputs are saved in `exact_prime_fourier_checks.json`. The generator
never starts a standard-basis or counting subprocess.

The full-run script `exact_algebra_backend_full_prime29_all.sing` was audited
independently without running Singular. The checker parsed and rebuilt every
polynomial from geometry: ordinary `F29`, 100 variables, all 100 domains
`z_i^3-1`, all 80 nonconstant moments, and no prefix or symmetry normalization.
Its SHA256 and multiplier-1 check are saved in
`exact_prime_fourier_full_import_review.json`. This audits the input scope, not
whether the standard-basis run finishes.

Reproduce checks and exports with:

```sh
python experiments/exact_prime_fourier.py --check
python experiments/exact_prime_fourier.py --prime 29 --all-moments experiments/example_prime29.json
python experiments/exact_prime_fourier_import_check.py
```

Separate backend runs and resource limits belong to the algebra experiment;
this generator report claims no unrestricted numerical count.
