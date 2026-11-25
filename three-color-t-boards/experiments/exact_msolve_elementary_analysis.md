# Exact change of coordinates after the elementary-constraint failure

The next concrete candidate is an invertible prefix-sum change of variables,
ordered by the cells' four role-membership signatures. It keeps 96 free
variables and the same unrestricted quotient dimension, but replaces the
large expanded pivot-domain equations with sparse cubics. Its ordinary
polynomial model and adapter have passed independent algebra/input review.
The transformed known nine-row prefix also has the expected six completions.
The unrestricted count remains unevaluated by this analysis.

The original augmented run did not reach its first printed degree-four
matrix dimensions. Its terminal result is `BACKEND_ERROR`, signal 11,
121.120406 CPU seconds and 134.879057 wall seconds. There is no completed
basis or count. The log alone localizes the failure only to the interval
between selecting degree-four pairs and printing the completed matrix
description; it does not prove which allocation or construction operation
failed. No new solver or debugger replay was performed for that run.

The added eight polynomials raised quadratic rank from six to ten, while
the number of distinct initial leading monomials remained 127. Their leading
terms therefore collided with existing leading terms. The first degree-two
round grew from two to six new polynomials, and the degree-three rounds
became substantially denser:

| Measured quantity | Original reduced model | With eight elementary equations |
| --- | ---: | ---: |
| Input terms | 37,146 | 48,842 |
| Distinct input monomials | 28,343 | 34,837 |
| Largest degree-three matrix width | 76,569 | 151,288 |
| New degree-three polynomials | 31 | 44 |
| Their total support entries | 618,643 | 3,210,256 |
| Average support per new degree-three polynomial | 19,956 | 72,960 |
| Pending pairs before first degree-four round | 217 | 345 |

The source's `find_multiplied_reducer` takes the first dividing current
basis leading monomial (`symbol.c:495` onward). `symbolic_preprocessing`
then recursively adds reducer multiples for newly discovered columns
(`symbol.c:558–608`). Dense lower-degree polynomials consequently make
later symbolic closure expensive even when the selected-pair batch is
small. These measurements explain why stronger equations did not yield
smaller matrices in the original coordinates. They do not establish a
precise degree-four matrix size for the failed augmented run.

The unchanged full bitset run completed three degree-four rounds and then
exited nonzero with the checked `MSOLVE_F2_BITSET_ERROR: allocation failed`
at the fourth, 19,153 by 2,615,528 matrix (printed density 0.20%). It used
133.624 CPU seconds and 145.619429 wall seconds. The three completed rounds
had already produced 47,801,704 sparse output terms. Packing transient
pivots helped it pass the previous null-row-allocation point, but the
persistent sparse basis, current reducer rows and two monomial tables
still consumed memory. This is a different failure from the augmented
run's unclassified signal 11. Neither failure means zero solutions.

The exact input/round statistics are in
`exact_msolve_elementary_analysis_comparison.json`.

## Coordinate certificate

Write each cell's signature as membership in `T,L,M,R`. Order the twelve
nonempty signature groups as

```
1001, 1000, 1010, 1011, 1111, 1110, 1100,
0100, 0110, 0111, 0011, 0001
```

Within each group use increasing original cell index. Consecutive signatures
differ in exactly one bit; all 81 top-role cells come first. Let `order[j]`
be this permutation and define over F2

```
y_j = sum_{k=0}^j z_order[k]
z_order[j] = y_j + y_(j-1),   y_(-1)=0.
```

These maps are inverse linear polynomial substitutions, not merely maps on
sampled points. The four unary Fourier equations telescope to

```
T: y80 = 0
L: y16 + y97 = 0
M: y8 + y72 + y81 + y98 = 0
R: y7 + y9 + y65 + y82 + y99 = 0.
```

Their supports are disjoint, so eliminate exactly

```
y80 = 0
y16 = y97
y81 = y8 + y72 + y98
y99 = y7 + y9 + y65 + y82.
```

The 96 remaining `y` coordinates are ordered increasingly; exported `x1`
through `x96` mean this ordered free list. These are sums of colors and may
be zero. For example, the independent review found 21–24 zero free prefix
coordinates in each of five published valid boards. Imposing `y_i^3+1`
would destroy legitimate solutions.

Instead, retain **all 100 original color-domain equations**, after the
linear substitutions: each has the form `L_cell(y)^3+1`. Original colors
become short linear forms: two have one term, 95 have two terms, and one
each has three, four and five terms. Their 100 cubics contain only 532 terms
in total; the largest has 26. Terms are represented by ordinary exponent
vectors. No exponent is reduced modulo three in the transformed ring.

Linear change of variables is a polynomial-ring automorphism. Quotienting
by the four displayed independent linears is an isomorphism to the ring
with the substituted generators and 96 remaining variables. Thus the new
ideal's vector-space dimension over F2 is exactly that of the original
Fourier/domain ideal. By the previously established scalar-extension and
radical-domain argument, that dimension is the full labeled board count.
There is no prefix restriction, normalization, field-extension divisor or
symmetry multiplier in this full model.

The all-moments export retains 72 nonzero moments; the eight unary moments
vanish after substitution. The representative export retains 36 nonzero
members of the usual 40 Frobenius classes. The omitted partners remain
consequences under the transformed original cubic domains. Every emitted
moment is expanded directly from all 81 geometric placements; it is not
formed by an invalid free-coordinate `y^4=y` or `y^3=1` reduction.

## Size and optional redundant equations

| Quantity | Original reduced all80 | Prefix-coordinate all80 |
| --- | ---: | ---: |
| Variables | 96 | 96 |
| Generators | 172 | 172 |
| Domain terms | 13,378 | 532 |
| Moment terms | 23,768 | 42,720 |
| Total terms | 37,146 | 43,252 |
| Largest polynomial | 6,321 | 1,234 |
| Distinct initial leading monomials | 127 | 139 |
| Maximum ordinary total degree | 8 | 8 |

The total input term count increases, so this is not a claim of an overall
size reduction or a guaranteed speedup. The concrete benefit is removing
very large cubic pivot polynomials and substantially shortening the added
histogram constraints. Their four quadratic supports become 159, 69, 35,
45 terms; adding their ordinary squares gives only 616 terms in eight
polynomials, compared with 11,696 before the coordinate change.

The top-role simplification can be seen directly. Under `y80=0`,

```
e2(z_order[0], ..., z_order[80])
  = sum_{i=1}^79 y_i*y_(i-1) + sum_{i=0}^79 y_i^2.
```

The other eliminations are then substituted ordinarily. The eight exported
elementary polynomials are consequences of the full exact ideal, as in the
existing elementary-generator proof. The four partners are literal ordinary
squares here, not `e4` equations and not squares reduced modulo independent
free-coordinate cubics.

An independent optional block contains 96 equations `y_i^4+y_i`. Their
membership is explicit, before and after the four linear eliminations:

```
y_j^4+y_j = sum_{k=0}^j z_order[k] * (z_order[k]^3+1).
```

Thus they preserve the ideal and count, while exposing pure quartic bounds.
They permit zero values and must not be replaced by Boolean relations.
The parent task's separate prefix-chain probes show that these valid quartics
do not automatically resolve Gröbner complexity. A length-12 zero-sum chain
has quotient dimension 132,861 with or without them; both completed exports
have the same 16 leading monomials (0.233/0.129 seconds elapsed). Both
length-30 versions reached their 12-second wall limits without a completed
basis. These are separate domain-chain fixtures, not T-board counts;
`exact_prefix_chain_probe_results.json` preserves their exact scope and
statuses. The full model still needs a bounded, separately recorded
computation.

## Reproducible artifacts and validation

- `exact_msolve_elementary_analysis.py` generates the certificate, explicit
  polynomials, statistics and one unevaluated input. It performs no solver
  call. It evaluates 4,400 domain/moment/elementary comparisons on random
  assignments over **all** of F4, including zero coordinates.
- Frozen model: `exact_msolve_elementary_analysis_prefix_gray_model.json`,
  SHA256 `7f8251ab52e8d6869c19cc861dc98b0c1e66904313b0d87920d9f95659700092`.
  Generator SHA256:
  `f33b64d51a4ee147cbd65f83c8c312965ff18c2ba171ca7d41fb35fa7307c1f2`.
- Adapter: `exact_msolve_prefix_sums.py`, function
  `prefix_definitions(all_moments=False, histogram_e2=False,
  field_equations=False)`. Its frozen-input checksum is mandatory. Metadata
  separately preserves `prefix_model_source_sha256` as well as the emitted
  input hash. All eight option combinations pass shape/hash checks.
- `exact_pivot_review_prefix_results.json` records the independent audit:
  all 276 possible source polynomials regenerated with tuple monomials,
  coordinate inverse checks, all quartic membership identities, five known
  witnesses, and all eight actual backend/prepare-only variants. No solver
  was run by this audit.
- `exact_msolve_elementary_analysis_fixture_results.json` records eight
  tiny completed coordinate fixtures. Exhaustive F4 enumeration and both
  bigint standard-monomial counters agree: independent-color cubes give
  9/27; a legal zero prefix coordinate gives three; fully fixed valid/invalid
  inputs give one/zero; a three-color covering fixture gives six, or two
  after normalization; optional quartics preserve nine.
- `exact_msolve_elementary_analysis_six_fiber.json` records the one authorized
  known nine-row prefix test, using all moments, elementary equations and
  quartics. Append 81 original-color linear constraints and one auxiliary
  `a^2+a+1`; this is 97 variables and 358 generators. The complete 108-element
  leading ideal has quotient dimension 12 by both bigint counters. Dividing
  by the two conjugate choices of `a` gives **six** completions.
- `exact_pivot_review_six_fiber_results.json` independently verifies all 358
  actual specialized polynomials, the variable-name alias, all 108 leading
  monomials and both quotient counts without a solver rerun.

The six-fiber solver printed one completion marker and reported 3.17 elapsed
and 3.14 CPU seconds, within its 60-second child, 90-second outer and 2 GiB
limits. The initial local postprocessor rejected the auxiliary name `a`
because the shared parser expects names `x1..x97`. Recovery verified the
actual exact variable header and used only an `a`→`x97` identifier alias for
parsing; the raw input/export and their hashes were preserved. No solver was
rerun. The outer traceback and recovery are explicitly recorded. Precise
subprocess timing was not persisted before that parser exception, so the
reported solver times are not presented as the lost high-precision rusage
measurements. The independent reviewer also corrected base-only metadata
for the fixed cell list and equation labels; these corrections are logged
without changing the actual input or basis.

Only tiny fixtures and the authorized fixed fiber were solved in this task.
No unrestricted solver computation, backend patch or new solver build was
launched by this analysis.
