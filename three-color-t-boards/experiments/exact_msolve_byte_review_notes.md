# Independent review of the eighth, checked-byte msolve build

Verdict: **PASS for the stated ordinary-F3 export scope**, at executable SHA-256
`63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76` and patch
`b97f1f487c27c2a0ddf7641046c36d118451a6231ce3554a69be25e0f24f04c6`.
This review did not start an unrestricted board solve. It establishes neither
completion of that computation nor a full board count.

## Source and arithmetic scope

The comparison against the preserved seventh source found exactly six changed
files (`main.c`, `data.h`, `engine.c`, `hash.c`, `io.c`, `symbol.c`) and two new
guard headers. All eight source hashes match the frozen provenance manifest.
The earlier rejected executable is not covered by this verdict.

The raw file guard executes before the upstream parser converts integers.
It restricts headers and polynomial syntax, bounds integer magnitudes and
variable indices, and rejects duplicate factors and malformed exponents.
The semantic guard checks the parsed CLI model, and it executes again inside
the common `import_input_data` before exponent-vector writes. The latter covers
the prime CLI's modular initialization path, which bypassed the first draft's
engine-only guard. The additional engine/core checks remain present.

The accepted computation is characteristic 3, DRL, one thread, exact sparse
LA option 2, no tracing/signatures/normal forms/elimination, reduced ordinary
g1/g2 export. Every variable has an explicit nonzero scalar multiple of
`x_i^3-x_i`, with 1 through 127 variables. Every other initial term has each
coordinate at most two. Alternative presentations that are mathematically
equivalent but fail these syntactic restrictions may be rejected safely.
The CLI's existing `-g` normalization can clamp larger positive values to 2;
the effective mode, which is what matters here, is checked as 1 or 2.

I inspected all exponent-typed sites in the source, including the ordinary
initialization, symbolic preprocessing, final interreduction, order comparison,
hash copying/reset, and promotion/staging paths. Active exponent construction
consists of checked input conversion and degree sums, coordinate maxima with
checked LCM degree sums, checked multiplier subtraction, checked term
multiplication, zero initialization, or copies of previously checked values.
The otherwise apparent `deg_t` to `exp_t` conversions in `spair_degree_cmp`
are inside `#if 0`. Signature, saturation, normal-form and post-export solving
paths are outside the accepted execution scope. Final interreduction uses the
same checked multiplication and symbolic-reducer routines. Order comparisons
operate on promoted integer values; allocations, contiguous-vector strides,
copies and staging lengths use `sizeof(exp_t)`. No active uint16-specific
exponent copy or packed exponent operation was found.

The mathematical degree argument is sound within that scope. Pure-cube leading
monomial coverage is preserved when a redundant basis element is removed:
a surviving leading monomial divides it. Symbolic preprocessing marks every
reducible column, and ordinary new basis rows have support only in the remaining
columns. Thus new basis terms have coordinate exponents at most two. Initial
exceptions are pure cubes. Pair LCM degrees are bounded by
`max(6,2*n+1)`, hence at most 255 for `n<=127`, and at most 193 for the actual
96-variable input. DRL tail degrees cannot exceed the leading degree, so
recursive reducer multiples and final reduction preserve the total-degree
bound. A small fixed bound on each recursively introduced coordinate, such as
five, is not needed and was not assumed. Runtime checks fail before narrowing
even if a future computation violates the mathematical invariant.

Changing storage width does not change polynomial coefficients, exponents,
domains, variable order, quotient dimension or any symmetry factor. Checked
arithmetic exits and allocation errors are not completed bases. Existing
strict normal-exit, marker, diagnostic, basis parsing and independent counting
requirements still apply.

## Independent completed calculations

`exact_msolve_byte_review.py` and its JSON report record 20 small ideals and
80 native executions: g1 and g2 for the preserved seventh build and for the
candidate. Each candidate export is byte-identical to the preceding build.
Full bases and leading monomials independently match the Python integer
Buchberger implementation; all 20 quotient dimensions match exhaustive
enumeration of F3 points. Cases include pure field domains, the two-cube
degree-six edge, signed constraints, nonzero products, mixed chains, unit
ideals, reversed/scaled domains, zero/duplicate domains, int32 coefficient
boundaries and eight reproducibly generated mixed systems. Tiny initial hash
tables exercise storage growth in actual solver runs.

The same review independently rejects 34 invalid raw files or execution modes.
These include missing/split/zero-scalar/wrong-sign/cross-variable domains,
non-domain cubic terms, coefficient/exponent wrap, duplicate factors, malformed
syntax, wrong fields, 128 variables, unsupported LA/trace-related modes and
numeric option overflow. Each exits nonzero with no completed marker and no
nonempty basis. The zero-scalar-domain case is rejected by the upstream parser
before the model guard, which is also a valid fail-closed result.

Two initial review-script attempts are preserved: one compared list-shaped
parsed exponents with tuple-shaped reference exponents; the other expected a
colon in an upstream error diagnostic. These were review assertion-format
mistakes, not candidate failures. The final report reran and passed all cases.

`exact_msolve_byte_arithmetic_review.py` extracts the frozen source's actual
checked arithmetic, input-vector conversion, LCM and term-multiplication
functions into a separate ASan+UBSan harness. It passes all 65,792 valid byte
addition/subtraction pairs, 1,200 independently generated vector cases
(nonzero input offsets, LCMs, and two-term row products), and LCM degrees 6
and 255. Fourteen scalar/input/degree/product overflow or underflow cases
exit explicitly before narrowing. Insertion is a vector-capture stub, so
this harness makes no claim about allocation or probing; the native complete
basis comparisons exercise the integrated tables.

Finally, `exact_msolve_byte_raw_guard_review.c` runs the actual raw-file guard
against the frozen full minimum-fill input, without calling a solver. The
separate polynomial scan verifies 96 explicit field domains, 176 generators,
96,248 terms, maximum initial total degree 8 and all non-domain coordinates
at most two. The input hash remains
`b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`.
Its existing full-count scope and retained independent translation variable
are unchanged: divisor and multiplier remain one.

## Evidence and limits

Independent reports: `exact_msolve_byte_review_results.json`,
`exact_msolve_byte_arithmetic_review_results.json`, and
`exact_msolve_byte_raw_guard_review_results.json`. Raw fixtures, exports and
logs are retained under `exact_msolve_byte_review_runs`; the sanitizer source,
binary and log are adjacent to its Python driver. The owner separately reports
26 paired basis comparisons, 39 guard failures and its own arithmetic harness
under `exact_msolve_byte_exponent_tools`; those are supporting evidence, not
substitutes for the independent tests above.

The byte representation reduces exponent-slab storage at a fixed capacity.
Other allocations, temporary copies and later intermediate growth remain.
The review does not predict wall time, memory peak or eventual completion of
the unrestricted count.
