# Independent msolve adapter review

The field conversion in `exact_msolve_backend.py` is correct. If
`K=F_p[a]/(a^2+a+1)` and `J` is the fixed-prefix ideal over `K`, the ordinary
prime-field presentation obtained by adding the variable `a` and its defining
quadratic is the same algebra, viewed over `F_p`. Therefore

```text
dim_Fp(A) = 2 * dim_K(K[x]/J).
```

The requested raw prefix-completion count is the latter dimension, so division
by two is necessary and sufficient when quadratic coefficients are present.
The characteristic satisfies `p=2 mod 3`; the quadratic is irreducible and
separable. All cell domains `x^3-1` are separable as well. After scalar
extension the domain quotient is a product of fields, and adding constraints
selects factors without introducing multiplicity. Equivalently, the extra
variable has two conjugate embeddings, each with an equally sized conjugate
prefix fiber. These are not extra labeled boards to retain in the count.

If every substituted moment coefficient lies in the prime field, the
generator correctly omits the extra variable and uses divisor one. This
includes completely fixed valid boards: all moments vanish, and the adapter's
single dummy variable constrained to zero has quotient dimension one.
Completely fixed invalid boards produce a unit ideal and dimension zero.
The full unrestricted model has 100 variables, all 100 cubic domains, all
80 nonconstant moments, and divisor one.

The independent test `exact_msolve_review.py` imports the adapter but does
not import its Fourier generator for its oracle. It reconstructs the Cartesian
T geometry, retains integer fixed-root multiplicities, expands all 80 moments
over the ordinary variables, and parses the actual emitted polynomials.
Across primes 5, 29, and 83, it checks 39 unrestricted/fixed-prefix models and
5,150 individual polynomials. Prefixes include all three single-cell colors,
several caps, nine-row cases, and complete valid and invalid boards.

Tiny exhaustive root fixtures verify that adding the quadratic variable
changes geometric counts `3,1,1,6` into `6,2,2,12`, respectively, and that
division by two recovers the intended counts. These fixtures cover an
independent cubic domain, equality to `a`, equality to its conjugate, and
three cube roots with zero sum.

Two initial implementation issues were reported to the root agent and fixed
there; this reviewer did not edit the backend:

- A rejected rerun could overwrite the original input before detecting an
  existing basis file. Collision detection now precedes every artifact write,
  and a regression check confirms the previous input and basis survive.
- The leading-ideal parser originally accepted duplicate/conflicting headers
  and ignored diagnostic comments. It now requires a unique leading-ideal
  marker and complete, unique metadata, and rejects diagnostics and unknown
  comments. Twenty malformed-output fixtures are rejected.

Completion semantics were checked with a mocked subprocess only. Normal
completion and the unit ideal are accepted; nonzero exit, diagnostic output,
truncated export, and timeout are refused. In particular, a timeout remains
incomplete even when a syntactically complete basis file exists. With
`require_export_marker=True`, exactly one
`MSOLVE_PRIME_GB_EXPORT_COMPLETE` line is required: missing and duplicate
markers prevent both basis completion and leading-ideal export. The ordinary
stock compatibility path remains separately selectable without that flag.

The adapter now directs child stdout and stderr into the fresh `.log` file
during execution, opened exclusively. Final validation reads that retained
file; it does not rewrite it or introduce another accepted completion path.
The mocked tests verify log visibility before the process returns, retention
of output on timeout, and preservation of an existing log. A separate tiny
real validation, `exact_msolve_live_log_fixture.json`, returned exact count
six for the p29 three-root sum fixture with the required single completion
marker. That fixture is separate from this script's mocked process tests.

The patch agent owns source-level verification that the new marker follows a
successfully completed exact F4 calculation and flushed export, before any
machine-word staircase enumeration. The adapter's parser is not itself a
Gröbner-basis verifier. Its standard-basis attestation relies on this audited
backend path, process success, and complete export syntax. The two Python
counters operate on a completed leading ideal and use arbitrary-precision
integers; a disagreement, missing pure-power bounds, or nonintegral division
by the extension degree prevents a `COMPLETE` count.

Reproduce this review with:

```sh
python experiments/exact_msolve_review.py
```

Results and the reviewed backend source hash are retained in
`exact_msolve_review_results.json`. Mocked `COMPLETE` outcomes test control
flow only and are not new solver results. This review launches no actual
solver process and obtains no unrestricted numerical count.
