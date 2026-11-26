# Independent review of the eighth, checked-byte msolve build

Verdict: **PASS for the stated ordinary-F3 export scope**, for executable SHA-256 `63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76` and patch `b97f1f487c27c2a0ddf7641046c36d118451a6231ce3554a69be25e0f24f04c6`.

This review did not run an unrestricted board solve. It neither proves that the full computation will finish nor produces a full board count.

## Source and arithmetic scope

Comparing the eighth source tree against the seventh found six changed files (`main.c`, `data.h`, `engine.c`, `hash.c`, `io.c`, `symbol.c`) and two new guard headers. All eight file hashes match the frozen provenance manifest. The earlier rejected executable is outside this verdict.

The raw file guard runs before the upstream parser converts any integers. It restricts headers and polynomial syntax, bounds integer magnitudes and variable indices, and rejects duplicate factors and malformed exponents. The semantic guard checks the parsed CLI model and runs again inside the shared `import_input_data` before any exponent vectors are written. That second check covers the prime CLI's modular initialization path, which the first draft's engine-only guard missed. The engine and core checks remain in place as well.

Accepted runs must use characteristic 3, DRL order, one thread, exact sparse LA option 2, reduced ordinary `-g 1` / `-g 2` export, and no tracing, signatures, normal forms, or elimination. The system must have 1 to 127 variables, an explicit nonzero scalar multiple of `x_i^3-x_i` for every variable, and coordinate exponents at most 2 in all other initial terms. Equivalent systems written in other syntactic forms may be safely rejected. The CLI's existing `-g` normalization can clamp larger positive values to 2, and the effective mode is checked as 1 or 2.

I audited every exponent-typed site in the source, covering initialization, symbolic preprocessing, final interreduction, order comparison, hash copying/reset, and promotion/staging. Active exponent operations consist only of checked input conversion and degree sums, coordinate maxima with checked LCM degree sums, checked multiplier subtraction, checked term multiplication, zero initialization, or copies of previously checked values. The `deg_t` to `exp_t` conversions in `spair_degree_cmp` sit inside `#if 0`. Signature, saturation, normal-form, and post-export solving paths are outside the allowed scope. Final interreduction uses the same checked multiplication and symbolic-reducer code. Order comparisons work on promoted integers, and all allocations, contiguous-vector strides, copies, and staging lengths use `sizeof(exp_t)`. No active `uint16_t`-specific copy or packed operation remains.

The degree bound holds within this scope:

- Pure-cube leading-monomial coverage survives redundant basis removal because a surviving leading monomial divides the removed one.
- Symbolic preprocessing marks every reducible column, and ordinary new basis rows only use the remaining right-block columns, so new basis terms have coordinate exponents at most 2.
- Initial exceptions are pure cubes, so pair LCM degrees are bounded by `max(6, 2*n+1)` (at most 255 for `n <= 127`, and at most 193 for the 96-variable board input).
- Under DRL, tail degrees never exceed the leading degree, so recursive reducer multiples and final interreduction preserve the total-degree bound.

No fixed per-coordinate bound like 5 is assumed for intermediate symbolic terms. Even if a future input broke the mathematical invariant, the runtime checks exit before narrowing.

Changing exponent storage width leaves coefficients, exponents, domains, variable order, quotient dimension, and symmetry factors untouched. Checked arithmetic exits and allocation errors never count as completed bases. All existing requirements for normal exit, completion marker, clean diagnostics, basis parsing, and independent counting still apply.

## Independent completed calculations

`exact_msolve_byte_review.py` and its JSON report cover 20 small ideals across 80 native runs (`-g 1` and `-g 2` for both the seventh build and the candidate). Every candidate export is byte-identical to the seventh build. Full bases and leading monomials match an independent Python integer Buchberger implementation, and all 20 quotient dimensions match exhaustive F3 point enumeration. Test cases include pure field domains, the two-cube degree-6 edge case, signed constraints, nonzero products, mixed chains, unit ideals, reversed and scaled domains, zero and duplicate domains, `int32` coefficient boundaries, and eight reproducibly generated mixed systems. Tiny initial hash tables force table growth during actual runs.

The same script checks 34 invalid raw files and unsupported execution modes: missing, split, zero-scalar, wrong-sign, or cross-variable domains; non-domain cubic terms; coefficient and exponent wrap; duplicate factors; malformed syntax; wrong fields; 128 variables; unsupported LA or trace-related modes; and numeric option overflow. Every case exits nonzero with no completion marker and no nonempty basis. The zero-scalar-domain case is caught by the upstream parser before the model guard, which also fails closed.

Two early review-script bugs are preserved in the logs: one compared list-shaped parsed exponents against tuple-shaped references, and the other expected a colon in an upstream error message. Both were script assertion bugs, not candidate bugs; the final report reran and passed all cases.

`exact_msolve_byte_arithmetic_review.py` extracts the frozen checked arithmetic, input-vector conversion, LCM, and term-multiplication functions into a separate ASan+UBSan harness. It passes all 65,792 valid byte addition/subtraction pairs, 1,200 independently generated vector cases (nonzero input offsets, LCMs, and two-term row products), LCM degrees 6 and 255, and 14 overflow/underflow cases that exit before narrowing. Insertion uses a vector-capture stub, so this harness tests arithmetic rather than allocator or probing behavior; the full basis comparisons exercise the real tables.

Finally, `exact_msolve_byte_raw_guard_review.c` runs the actual raw-file guard on the frozen full minimum-fill input without launching a solver. A separate polynomial scan confirms 96 explicit field domains, 176 generators, 96,248 terms, maximum initial total degree 8, and all non-domain coordinates at most 2. The input hash remains `b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`, and the full-count scope with the retained translation variable keeps divisor and multiplier equal to 1.

## Evidence and limits

Independent reports are saved in:

- `exact_msolve_byte_review_results.json`
- `exact_msolve_byte_arithmetic_review_results.json`
- `exact_msolve_byte_raw_guard_review_results.json`

Raw fixtures, exports, and logs live under `exact_msolve_byte_review_runs`, and the sanitizer source, binary, and log sit next to the Python driver. The build owner's 26 paired basis comparisons, 39 guard failures, and arithmetic harness in `exact_msolve_byte_exponent_tools` are separate supporting evidence.

Byte storage shrinks the exponent slab at any fixed capacity, but other allocations, temporary copies, and later intermediate growth remain. This review makes no prediction about wall time, peak memory, or whether the unrestricted count will finish.
