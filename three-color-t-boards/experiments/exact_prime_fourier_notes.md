# Fourier ideals in odd prime characteristic

`exact_prime_fourier.py` reconstructs all 81 T placements from their row and
column geometry. It imports no characteristic-two polynomial lists and never
reuses coefficients canceled modulo two. It supports any experimentally sized
prime `p` congruent to 2 modulo 3, with exact primality validation; the checked
primes are **5, 29, and 83**.

## Field, equations, and exact count

Work with ordinary polynomial variables satisfying `z_i^3-1=0`. The quadratic
polynomial `a^2+a+1` is irreducible over `F_p`: otherwise `F_p` would contain a
nontrivial cube root of unity, contradicting `3` not dividing `p-1`. Its
extension field has the three distinct cube roots

```text
color 0 -> 1       color 1 -> a       color 2 -> -1-a.
```

For a role-exponent vector `e` in `{0,1,2}^4`, form the moment
`P_e = sum_over_placements product_over_roles z_cell^e_role`. The required
nonconstant moments vanish. The zeroth moment is automatically `81 mod p`;
it is not set to zero or replaced by one in odd characteristic.

The 81-character Fourier transform on the 81 patterns is invertible. Its
one-coordinate matrix is the Vandermonde matrix of three distinct roots,
and the full transform is its fourfold tensor product. The uniform count
vector has zeroth transform value 81 and all nonconstant values zero.
Consequently the moment conditions say every integer pattern count is
congruent to 1 modulo `p`. Each count is therefore at least one. Since all
81 counts sum to 81, all equal one. Thus the solution set is exactly the
valid boards for every allowed prime.

Because `p == 2 mod 3`, Frobenius gives `P_e^p = P_(2e mod 3)` modulo the
cubic domains. The default export keeps the **40** vectors whose first
nonzero entry is 1, one per nonconstant Frobenius pair. This remains valid
after fixing a prefix: Frobenius also conjugates its coefficients correctly.

`all_moments=True` exports **all 80** nonconstant moments. The 40 default
equation objects remain identical, and metadata records that the additional
40 equations are redundant. They may aid a standard-basis computation because
they are available explicitly instead of being derived through `p`th powers
and domain reductions. This is an equivalent generating ideal, not an
additional restriction.

The cubic domains are separable, since `p != 3`. After extending scalars to
`F_(p^2)`, their quotient splits as a product of fields, one factor per labeled
coloring. Adding the moments selects exactly the valid factors without
multiplicity. Therefore the ordinary `F_p` quotient dimension of the full
model already equals the full labeled board count: **multiplier 1**. Prefix
models with quadratic coefficients are computed over `F_(p^2)` and similarly
count extensions of that fixed prefix. No Boolean relations, color symmetry
normalization, or reflection normalization are introduced.

## Why 29 already supplies exact low-order margins

If all moments supported on a selected set of `k` roles vanish, inversion
gives each of its `3^k` marginal counts congruent to `3^(4-k)` modulo `p`.
When `p > 3^(4-k)`, every nonnegative count is at least this target, and their
total 81 forces equality for every category. Thus:

| Marginal order | Exact target per category | Sufficient prime threshold |
| --- | ---: | ---: |
| One role | 27 | `p > 27` |
| Two roles | 9 | `p > 9` |
| Three roles | 3 | `p > 3` |
| Four roles | 1 | `p > 1` |

Both 29 and 83 force exact one-role margins at the same low moment order.
Prime 29 is the smallest prime congruent to 2 modulo 3 above 27. These facts
give no reason to expect a distinct marginal-strength advantage from 83.
Prime 5 already forces exact three-role margins, but not by itself exact
one-role or two-role margins.

## API and coefficient handling

```python
from exact_prime_fourier import generate_model

full = generate_model(29)
full80 = generate_model(29, all_moments=True)
prefix = generate_model(29, prefix_rows, all_moments=True)
```

The schema has `coefficient_characteristic`, `variables`,
`free_original_cells`, explicit cubic `domain_equations`, and
`moment_equations`. Each term is:

```json
{"coefficient": [2, 28], "monomial": [[0, 1], [4, 2]]}
```

Here `[u,v]` means `u+v*a`, and variable indices refer to the zero-based free
variable list. Fixed-prefix colors are substituted before term collection.
For each monomial the generator first retains its **integer** multiplicities
`n0,n1,n2` at the three roots, then computes the coefficient
`[(n0-n2) mod p, (n1-n2) mod p]`. The unreduced multiplicities are retained
in `integer_occurrence_groups`, so cancellation is specific to the selected
prime. All generated models remain marked `standard_basis_complete=False`.

The algebra backend imports this schema using `prime:29` for 40 equations
or `prime-all:29` for 80. It uses ordinary `F29` when coefficients are in the
prime field, and the quadratic extension with the stated minimal polynomial
when necessary for a fixed prefix.

## Verification and full-import audit

At **each** of 5, 29 and 83, the checks passed:

- 2,400 comparisons between exported equations and a separately evaluated
  Fourier transform of direct integer pattern counts on random boards, with
  prefix lengths 0, 1, 6, 9 and 10.
- 2,400 evaluations of explicitly exported Frobenius partners, checking
  equality to the representative's `p`th power and equality of the default
  equations to the corresponding all-80 subset.
- All 80 equations on **1,557 distinct explicit witness boards**, deduplicated
  from the published seeds, `extended_seeds.json`, and the gauge certificate.
- Five fully fixed valid boards, each giving the zero ideal in zero free
  variables; the known uniform-triple counterexample is rejected by eight
  representative equations and all sixteen corresponding all-80 equations.
- Tiny exhaustive root fixtures: nine ordered pairs of cube roots and six
  ordered root triples satisfying `x+y+z=0`.

Results are in `exact_prime_fourier_checks.json`. The generator launches no
standard-basis or counting subprocess.

The actual full-run script `exact_algebra_backend_full_prime29_all.sing`
was audited independently, without invoking Singular. The audit parsed and
regenerated every polynomial from geometry: ordinary `F29`, 100 variables,
all 100 domains `z_i^3-1`, all 80 nonconstant moments, and no fixed prefix or
symmetry normalization. Its SHA256 and the multiplier-1 conclusion are in
`exact_prime_fourier_full_import_review.json`. This verifies input scope, not
completion of the standard-basis calculation.

Reproduce checks and exports with:

```sh
python experiments/exact_prime_fourier.py --check
python experiments/exact_prime_fourier.py --prime 29 --all-moments experiments/example_prime29.json
python experiments/exact_prime_fourier_import_check.py
```

Separate backend runs and their limits are owned by the algebra experiment.
No unrestricted numerical count is claimed by this generator report.
