# Independent msolve adapter review

The field conversion in `exact_msolve_backend.py` is correct. For `K = F_p[a] / (a^2 + a + 1)` and a fixed-prefix ideal `J` over `K`, adding the variable `a` and its quadratic relation produces the exact same algebra over `F_p`, so:

```text
dim_Fp(A) = 2 * dim_K(K[x]/J).
```

Because the raw prefix-completion count is `dim_K(K[x]/J)`, dividing by 2 is both necessary and sufficient whenever quadratic coefficients appear. Every tested characteristic satisfies `p = 2 mod 3`, so both `a^2 + a + 1` and all cell domains `x^3 - 1` are separable (`a^2 + a + 1` is also irreducible). Over the algebraic closure, the domain quotient splits into a product of fields with no multiplicity. Put another way, `a` has two conjugate embeddings with equal-sized fibers, and dividing by 2 avoids double-counting them.

When every substituted moment coefficient already lies in `F_p`, the adapter omits `a` and sets the divisor to 1. For a completely fixed valid board, all moments vanish and the adapter's single dummy variable set to 0 gives dimension 1; a completely fixed invalid board gives the unit ideal and dimension 0. The full unrestricted model has 100 variables, 100 cubic domains, 80 nonconstant moments, and divisor 1.

`exact_msolve_review.py` imports the adapter without reusing its Fourier generator as an oracle. It rebuilds the Cartesian T geometry independently, tracks integer fixed-root multiplicities, expands all 80 moments over the variables, and parses the emitted polynomials. Across primes 5, 29, and 83, it verifies 39 unrestricted and fixed-prefix models totaling 5,150 polynomials (single-cell colors, caps, nine-row prefixes, and full valid and invalid boards).

Small exhaustive root fixtures confirm that adding `a` doubles geometric counts `3, 1, 1, 6` to `6, 2, 2, 12`, and dividing by 2 recovers the exact targets (covering an independent cubic domain, equality to `a`, equality to its conjugate, and three cube roots summing to 0).

Two early bugs were reported to the root agent and fixed without this reviewer editing the backend:

- A rejected rerun could overwrite the existing input file before checking for an existing basis file. Collision checks now run before any file write, backed by a regression test.
- The leading-ideal parser once accepted duplicate or conflicting headers and ignored diagnostic comments. It now requires a unique leading-ideal marker and complete, unique metadata, and rejects diagnostics and unknown comments (verified against 20 malformed fixtures).

Mocked subprocess tests check completion handling: normal runs and unit ideals pass, while nonzero exits, diagnostics, truncated exports, and timeouts fail (even if a syntactically complete basis file exists on disk). With `require_export_marker=True`, the log must contain exactly one `MSOLVE_PRIME_GB_EXPORT_COMPLETE` line; missing or duplicate markers block both basis completion and leading export. Stock msolve runs remain selectable when that flag is off.

Child stdout and stderr stream directly into a fresh, exclusively created `.log` file during execution, and final validation reads that saved file without rewriting it. Mocked tests confirm live log visibility, output retention on timeout, and overwrite protection. Separately, a small real run (`exact_msolve_live_log_fixture.json`) returned exact count 6 for the characteristic-29 three-root sum fixture with one completion marker.

Trust boundary: the patch agent verifies at the source level that the marker prints only after exact F4 finishes and the basis export is flushed, before machine-word staircase enumeration. The adapter's parser does not independently verify Gröbner bases; it relies on that audited backend, clean exit, and strict export parsing. Both arbitrary-precision Python counters must agree on the leading ideal, confirm pure-power bounds, and divide evenly by the extension degree before returning `COMPLETE`.

Reproduce this review with:

```sh
python experiments/exact_msolve_review.py
```

Results and the reviewed backend hash are saved in `exact_msolve_review_results.json`. Mocked `COMPLETE` results only test control flow; this review runs no solver and produces no unrestricted board count.
