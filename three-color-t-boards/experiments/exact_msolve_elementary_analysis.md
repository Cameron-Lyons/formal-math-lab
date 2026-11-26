# Exact change of coordinates after the elementary-constraint failure

The next candidate is an invertible prefix-sum change of variables ordered by each cell's four role-membership signatures. It keeps 96 free variables and the exact same unrestricted quotient dimension, while turning the huge expanded pivot-domain equations into sparse cubics. Its polynomial model and adapter passed independent algebra and input review, and the transformed nine-row prefix still gives the expected 6 completions. The unrestricted board count remains unknown.

## Why the elementary-constraint run failed

The augmented elementary-constraint run died before printing its first degree-4 matrix dimensions. Its terminal status is `BACKEND_ERROR` (signal 11) after 121.120406 CPU seconds and 134.879057 wall seconds, with no basis or count. The log only narrows the crash to the interval between selecting degree-4 pairs and printing the finished matrix dimensions; it does not identify which allocation or operation failed, and no debugger replay was run.

Adding those eight polynomials raised quadratic rank from 6 to 10 while leaving distinct initial leading monomials at 127, meaning their leading terms collided with existing ones. The first degree-2 round grew from 2 to 6 new polynomials, and degree-3 rounds became much denser:

| Measured quantity | Original reduced model | With eight elementary equations |
| --- | ---: | ---: |
| Input terms | 37,146 | 48,842 |
| Distinct input monomials | 28,343 | 34,837 |
| Largest degree-three matrix width | 76,569 | 151,288 |
| New degree-three polynomials | 31 | 44 |
| Their total support entries | 618,643 | 3,210,256 |
| Average support per new degree-three polynomial | 19,956 | 72,960 |
| Pending pairs before first degree-four round | 217 | 345 |

In msolve, `find_multiplied_reducer` picks the first basis leading monomial that divides a term (`symbol.c:495` onward), and `symbolic_preprocessing` recursively adds reducer multiples for each new column (`symbol.c:558-608`). Dense low-degree basis elements make later symbolic closure blow up even for small pair batches. These counts explain why stronger equations produced larger matrices in the original coordinates, though they do not pin down the exact degree-4 matrix size of the crashed run.

By contrast, the unchanged full bitset run finished three degree-4 rounds before exiting nonzero with `MSOLVE_F2_BITSET_ERROR: allocation failed` on the fourth matrix (19,153 by 2,615,528, printed density 0.20%). It ran for 133.624 CPU seconds and 145.619429 wall seconds, and its three completed rounds already created 47,801,704 sparse output terms. Packing transient pivots moved past the earlier null output-row crash, but the persistent sparse basis, reducer rows, and two monomial hash tables still filled memory. This checked allocation failure is separate from the augmented run's signal 11, and neither failure implies zero solutions.

Full input and round statistics are saved in `exact_msolve_elementary_analysis_comparison.json`.

## Coordinate certificate

Write each cell's role signature as a 4-bit string for membership in `T,L,M,R`, and order the 12 nonempty groups as:

```
1001, 1000, 1010, 1011, 1111, 1110, 1100,
0100, 0110, 0111, 0011, 0001
```

Sort cells within each group by increasing original cell index. Consecutive groups differ in one bit, and all 81 top-role cells come first. Let `order[j]` be this permutation, and define over F2:

```
y_j = sum_{k=0}^j z_order[k]
z_order[j] = y_j + y_(j-1),   y_(-1)=0.
```

These are inverse linear polynomial substitutions. The four unary Fourier equations telescope to:

```
T: y80 = 0
L: y16 + y97 = 0
M: y8 + y72 + y81 + y98 = 0
R: y7 + y9 + y65 + y82 + y99 = 0.
```

Their eliminated variables are disjoint, so we substitute:

```
y80 = 0
y16 = y97
y81 = y8 + y72 + y98
y99 = y7 + y9 + y65 + y82.
```

The remaining 96 `y` coordinates stay in increasing index order and are exported as `x1` through `x96`. Because these coordinates are sums of colors, they can equal zero: the independent review found 21 to 24 zero free coordinates in each of five published valid boards. Imposing `y_i^3 + 1` on them would drop valid boards.

Instead, we keep **all 100 original color-domain equations** `L_cell(y)^3 + 1` after substitution. Every original color becomes a short linear form: 2 have one term, 95 have two terms, and 1 each has three, four, and five terms. All 100 cubics together have just 532 terms, with at most 26 terms in any single equation. Terms use ordinary exponent vectors with no modulo-3 exponent reduction.

A linear coordinate change is a polynomial-ring automorphism, and quotienting by four independent linear equations gives an isomorphic 96-variable quotient ring. Over F2, this ideal has the exact same vector-space dimension as the original Fourier/domain ideal. By the earlier scalar-extension and radical-domain proof, that dimension equals the full labeled board count, with no prefix restriction, normalization, field-extension divisor, or symmetry factor.

The all-moments export keeps 72 nonzero moments (the 8 unary moments vanish after substitution). The representative export keeps 36 nonzero members of the usual 40 Frobenius classes, whose omitted partners follow from the transformed cubic domains. Every moment is expanded directly from all 81 placements without applying invalid `y^4 = y` or `y^3 = 1` reductions.

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

Total input terms go up slightly, so this change does not shrink the input overall or guarantee faster solving. Its benefit is eliminating huge cubic pivot equations and shrinking the optional histogram constraints: the four quadratic supports drop to 159, 69, 35, and 45 terms, so all eight polynomials (including their ordinary squares) total just 616 terms instead of 11,696.

For the top role, `y80 = 0` simplifies `e2` directly:

```
e2(z_order[0], ..., z_order[80])
  = sum_{i=1}^79 y_i*y_(i-1) + sum_{i=0}^79 y_i^2.
```

The other three eliminations are substituted ordinarily. By the existing elementary-generator proof, all eight polynomials belong to the exact ideal. The four partners are literal ordinary squares, not `e4` equations and not squares reduced modulo free-coordinate cubics.

An optional block adds the 96 quartic equations `y_i^4 + y_i`. Ideal membership is explicit both before and after elimination:

```
y_j^4+y_j = sum_{k=0}^j z_order[k] * (z_order[k]^3+1).
```

These quartics preserve the ideal and count while giving pure quartic bounds on every variable. They allow zero values and must not be replaced by Boolean relations. Separate prefix-chain probes show they do not automatically solve Gröbner complexity: a length-12 zero-sum chain gives quotient dimension 132,861 with or without them, producing the same 16 leading monomials in 0.233 and 0.129 seconds, while both length-30 variants hit their 12-second wall limits without finishing. Those probes are domain-chain fixtures recorded in `exact_prefix_chain_probe_results.json`, not T-board counts. The full model still needs its own bounded run.

## Reproducible artifacts and validation

- `exact_msolve_elementary_analysis.py` builds the certificate, polynomials, statistics, and one unevaluated input without invoking a solver. It runs 4,400 domain, moment, and elementary checks on random assignments across **all** of F4, including zero coordinates.
- Frozen model: `exact_msolve_elementary_analysis_prefix_gray_model.json`, SHA-256 `7f8251ab52e8d6869c19cc861dc98b0c1e66904313b0d87920d9f95659700092`. Generator SHA-256: `f33b64d51a4ee147cbd65f83c8c312965ff18c2ba171ca7d41fb35fa7307c1f2`.
- Adapter: `exact_msolve_prefix_sums.py`, exposing `prefix_definitions(all_moments=False, histogram_e2=False, field_equations=False)`. It checks the frozen-input SHA-256, records `prefix_model_source_sha256` alongside the emitted input hash, and passes shape and hash checks for all eight option combinations.
- `exact_pivot_review_prefix_results.json`: independent audit regenerating all 276 source polynomials with tuple monomials and checking coordinate inverses, all quartic membership identities, five known valid boards, and all eight prepare-only variants without running a solver.
- `exact_msolve_elementary_analysis_fixture_results.json`: eight tiny completed coordinate fixtures where exhaustive F4 enumeration and both bigint standard-monomial counters agree (independent-color cubes give 9 and 27; a legal zero prefix coordinate gives 3; fully fixed valid/invalid inputs give 1 and 0; a three-color covering fixture gives 6, or 2 after normalization; optional quartics keep 9).
- `exact_msolve_elementary_analysis_six_fiber.json`: the single authorized nine-row prefix test with all moments, elementary equations, and quartics, plus 81 original-color linear constraints and one auxiliary `a^2 + a + 1` (97 variables, 358 generators). Both bigint counters give quotient dimension 12 on the 108-element leading ideal; dividing by the 2 conjugate choices of `a` gives **6** completions.
- `exact_pivot_review_six_fiber_results.json`: independent check of all 358 specialized polynomials, the variable-name alias, all 108 leading monomials, and both quotient counts without rerunning the solver.

The six-fiber run emitted one completion marker and reported 3.17 elapsed seconds and 3.14 CPU seconds, well inside its 60-second child, 90-second outer, and 2-GiB limits. The initial postprocessor rejected the auxiliary variable name `a` because the shared parser expects `x1..x97`. Recovery verified the exact header and parsed with an `a` to `x97` identifier alias while leaving the raw input, export, and hashes untouched and without rerunning the solver. Because the parser exception occurred before high-precision subprocess timings were saved, the solver's printed times are recorded directly rather than as rusage totals. The independent reviewer also logged base-only metadata fixes for the fixed cell list and equation labels without changing the input or basis.

Only tiny fixtures and the authorized nine-row fiber were solved here; no unrestricted solve, backend patch, or new solver build was started.
