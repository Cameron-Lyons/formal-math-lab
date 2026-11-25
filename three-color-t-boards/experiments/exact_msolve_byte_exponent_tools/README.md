# Eighth preserved build: checked byte exponents

This is a dedicated ordinary-F3, serial, exact sparse DRL basis-export executable. It stores each exponent lane in one byte without reducing exponents modulo 256 or changing polynomial identities. Every reachable narrowing arithmetic operation is checked before assignment. Overflow or unsupported input exits nonzero before the completed-basis marker.

Executable: `msolve`, SHA-256 `63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`. The complete patch against the preserved seventh build is `checked-byte-exponents.patch`, SHA-256 `b97f1f487c27c2a0ddf7641046c36d118451a6231ce3554a69be25e0f24f04c6`. `source.json` records the upstream v0.11.0 archive/commit, all predecessor patches, source/compiler/library hashes and build commands. Previous builds are unchanged. No full-board solve was run for this build.

## Accepted scope

The standalone executable accepts ASCII expanded-polynomial files with canonical header `x1,...,xn`, characteristic 3, and 1 through 127 variables. Each variable must have an explicit two-term nonzero scalar multiple of `x_i^3-x_i` among the initial generators. Every other initial monomial must have each coordinate at most two. A redundant field equation, zero polynomial or unit polynomial is permitted when all field domains are also present; unsupported presentations are conservatively rejected rather than silently rewritten.

Raw input is validated before the upstream parser's integer conversions. The narrow grammar accepts integer coefficients within signed-int32 magnitude and monomial factors with nonnegative byte-range exponents, checks variable names, rejects repeated factors and malformed tokens, and bounds term/generator counts. It accepts the repository's actual generated model syntax. Alternative variable headers, rationals, factored expressions, negative exponents and numeric overflow are outside this executable's interface.

Only ordinary flags for file/output, g1/g2 export, LA option 2, one thread, reduced basis, genericity handling 0, verbosity, hash sizing/reset and pair batch target are accepted. QQ, other fields, signature methods, normal forms, saturation/colon, elimination, parametrization, binary input and non-export paths are rejected. The core and common import functions repeat field/order/mode checks, so the scope does not depend solely on the command-line dispatch. Final interreduction is supported with the same checked exponent arithmetic.

## Why one byte is sufficient for these models

Initially, every non-domain monomial has each exponent at most two, and each exceptional domain is a pure cube minus its variable. The active leading-monomial ideal contains each pure cube. Removing a redundant basis element preserves this coverage because the surviving leading monomial divides the removed one (`update.c` and `f4.c`).

Ordinary symbolic preprocessing visits every introduced monomial, marking a left pivot whenever an active leading monomial divides it (`symbol.c:find_multiplied_reducer`, `symbolic_preprocessing`). The column partition places these pivots on the left (`convert.c:convert_hashes_to_columns`), and the exact sparse reducer exports new rows only from the right block (`la_ff_8.c:reduce_dense_row_by_known_pivots_sparse_ff_8`). Therefore every monomial in a newly produced ordinary basis polynomial is irreducible by every pure-cube divisor and has coordinate exponents at most two.

The LCM of two such leading monomials has total degree at most 2n. The LCM of a pure cube and one such leading monomial has degree at most 2n+1. The LCM of two pure cubes has degree at most six. Hence the uniform bound is `max(6, 2n+1) <= 255` for 1 <= n <= 127. The six term matters for n=2; the bound for the actual 96-variable board models is 193.

Under DRL, every tail has degree no larger than its leading monomial. Multiplying a reducer to cancel a symbolic term therefore never increases degree. This applies recursively throughout symbolic preprocessing and final interreduction. Individual symbolic coordinates need not stay at most five: repeated reductions can redistribute degree. The total-degree bound, which also bounds every nonnegative coordinate, is the valid invariant.

This mathematical argument supports the scope restriction. Runtime checks remain necessary independently of it: `checked_exp_value` rejects values outside [0,255], `checked_exp_add` widens before adding, and `checked_exp_sub` widens before subtracting. Input-vector reads and degree accumulation, pair-LCM degree accumulation, polynomial multiplication, and pair/reducer multiplier differences use these helpers. Copies, maximum selections, hashing and comparisons preserve already checked values. The inactive signature-add helper is checked too. Normal-form, signature, saturation, elimination and tracing computations are excluded rather than relying on this degree proof.

## Storage and compatibility

`exp_t` changes from uint16 to uint8. Ordinary exponent vectors include the total-degree lane: the actual 96-variable model has 97 lanes. All active allocations, copies, pointer strides, staging and reset paths use `sizeof(exp_t)`. The exponent comparisons and hash operations are scalar; the AVX coefficient kernels operate on separate coefficient types and are unchanged. The whole pinned solver and its static project libraries are rebuilt with the same typedef; this is not an ABI substitution into the older libraries.

Thus a 97-lane exponent vector occupies 97 rather than 194 bytes. Metadata, bucket arrays, pointers, sparse row indices and coefficients do not shrink. At the previous 3-GiB minimum-fill trial's failed symbolic target of 5,505,024 slots, the exponent slab would shrink by 509.25 MiB; at its latest reported basis capacity 3,801,088 it would shrink by another 351.625 MiB. These are same-capacity calculations, not measured peak process-memory savings. Other arrays, realloc transient copies and unchecked upstream allocations can still cause failure. No speed or full-count completion guarantee follows.

## Validation

`validation.json` records 26 paired completed g1/g2 comparisons against the seventh executable, with byte-identical exports, exactly one completion marker and no error diagnostics. Eleven small F3 models agree with exhaustive enumeration and both independent integer staircase counters. The natural-F3 nine-row board fiber gives quotient dimension 6 directly. The 127-independent-domain fixture gives exact dimension 3^127, checking the maximum supported variable count and large integer counting path. No unrestricted board model was solved.

`guard_check.json` records 39 fail-nonzero parser/model/mode cases: missing or wrongly signed domains, unreduced non-domain terms, field mismatches, malformed variables/factors, huge exponents and coefficients, negative/missing exponents, total degree 381, 128 variables, option integer wrap and unsupported execution modes. Every case lacks both completion marker and nonempty basis export.

`arithmetic_check.py/.c/.json` extracts the actual arithmetic functions, input-vector conversion, LCM construction and polynomial multiplication. ASan+UBSan passes all 65,792 valid byte additions/subtractions, all 256 scalar values, input degrees 254 and 255, and an actual 127-variable LCM of degree 255. Eleven synthetic input/add/subtract/LCM/product overflow or underflow cases exit explicitly before narrowing. Its hash insertion is a vector-capture stub, so this harness does not claim to test allocator or probing behavior; the complete basis comparisons exercise the integrated table paths.

The original draft is preserved in `rejected_attempt1/`. A missing-domain test showed that guarding only `initialize_gba_input_data` missed the prime CLI's `initialize_modular_trace` route. The candidate now checks the parsed CLI model and the common `import_input_data` boundary, with the original engine guard retained. No full trial used the rejected draft. The valid-model comparisons were repeated after this fix. A later comment-only correction changed the proof formula to max(6,2n+1); a rebuild verifies identical executable bytes.

Independent review passed on exactly the frozen source,
patch and executable above. Its 20 independent small ideals produced 80 g1/g2
exports agreeing with the seventh build, Python Buchberger and direct F3
enumeration; 34 independent parser/scope cases rejected. Actual-source
ASan+UBSan arithmetic tests passed 65,792 byte cases, 1,200 input-index/LCM/
two-term-product cases, the degree-six and degree-255 boundaries, and 14
failure cases. The actual unrestricted minimum-fill input passed its source-only
raw/model audit, without a solver run. See
`../exact_msolve_byte_review_notes.md`,
`../exact_msolve_byte_review_results.json`, and
`../exact_msolve_byte_arithmetic_review_results.json`.

## Reproduction

`prepare.py` extracts the pinned source and applies recorded predecessor patches, then applies `finish_scope_fix.py`; it refuses to replace an existing source directory. `build.py` builds with `-O2 -g0`, static project libraries, no OpenMP and `make -j1`, using local dependencies in `../exact_algebra_backend_root/usr`. `validate.py`, `guard_check.py` and `arithmetic_check.py` preserve input, output and logs. Solver comparisons use a 20-second child wall limit and 2-GiB address-space limit; rejection cases use ten seconds. Use a fresh artifact directory for reproduction because saved solver outputs are not overwritten.
