# Independent F4 basis backend

The unrestricted ternary board count remains unknown. This backend runs msolve's F4 algorithm with exact sparse linear algebra, then counts standard monomials of the completed leading ideal using two independent Python big-integer counters. Neither a prepared polynomial input nor an unfinished F4 run yields a board count.

## Provenance and exact arithmetic

Stock msolve `0.11.0-1` was extracted locally from the official Arch package after verifying its checksum against the repository database (`exact_msolve_tools/package.json`). `exact_msolve_setup.py` reproduces the extraction, reusing the local runtime dependencies from the earlier algebra setup with no system package installation. An earlier stalled upstream download was cancelled before using this package.

The [official msolve documentation](https://github.com/algebraic-solving/msolve/blob/master/README.md) specifies `-g 1` for leading-ideal export and `-g 2` for full-basis export, and the pinned help text and source confirm `-l 2` selects exact sparse linear algebra. Our runner passes `-l 2 -t 1 -r 1 -c 0`: exact sparse linear algebra, one thread, reduced basis, no variable-order change, and no random linear form. The random seed printed in the log does not alter this deterministic finite-field path.

Even under `-g 1`, stock msolve computes a machine-integer staircase size after writing the export, which can overflow or exhaust memory on compact ideals with huge quotients. Our [first patched build](exact_msolve_patched_tools/README.md) checks for F4 errors, writes the prime-field basis, prints one `MSOLVE_PRIME_GB_EXPORT_COMPLETE` marker, and returns before staircase enumeration without altering F4 itself. Twelve small stock-vs-patched exports match byte-for-byte. On 100 independent cubic domains, both versions write the same leading ideal; the patched build exits cleanly and both Python counters return:

```text
515377520732011331036461129765621272702107522001 = 3^100
```

Trust boundary: this workflow trusts msolve's completed exact F4 basis. Counting its leading monomials independently checks staircase arithmetic but does not independently certify Buchberger's criterion or ideal membership.

## Model and fixed-prefix extension

The first unrestricted input uses the ordinary F29 polynomial ring with 100 variables, all 100 cubic domains `x_i^3 - 1`, and all 80 nonconstant Fourier sums. Its quotient dimension equals the full labeled board count directly (divisor and symmetry multiplier are both 1), with no Boolean reduction. The [actual-file audit](exact_parity_math_msolve_audit.json) independently reconstructed all placements from centered Cartesian coordinates and verified every polynomial.

Fixed prefixes can introduce coefficients in `F29^2`. When quadratic coefficients appear, the adapter adds an ordinary variable `a` with `a^2 + a + 1 = 0` (colors `1, a, -a - 1`). Viewing the algebra over F29 doubles the vector-space dimension, so the count divides by exactly 2. When all specialized coefficients lie in F29, `a` is omitted and the divisor is 1.

The [independent adapter review](exact_msolve_review_notes.md) verified 5,150 polynomials across 39 geometric models, field-degree accounting, strict output parsing, overwrite protection on rejected reruns, and error/completion handling. Both Python counters use arbitrary-precision integers. A run reaches counting only after a clean exit, a complete fresh export with unique matching metadata, zero diagnostics, and (for patched builds) exactly one completion marker.

## Completed checks and early full-board trials

Small stock fixtures confirm expected ordinary-ring behavior: dimensions 3 and 9 for one and two cubic domains, 6 for the three-root zero-sum fixture, 0 for the unit ideal, and dimension 3 for an ordinary F2 cubic (confirming no silent Boolean reduction).

On the known nine-row six-completion fiber, both stock and patched builds finish with F29 quotient dimension 12 (including the quadratic variable `a`), giving exactly 6 boards across both counters. A patched 10-variable pure-power fixture returns `10^20` (above 64-bit integer range). A reduced 21-variable binary trial timed out at 30 wall seconds without reproducing the known binary total of 168.

Early unrestricted runs under a 2-GiB address-space cap:

- **`exact_msolve_full_prime29_all.ms`** (plus `.log`, `.json`, `.outer.log`, `.outer.json`; input SHA-256 `4f3610b250e309bb1f5f722c6c621354f8078e0fc91df5e5e860edd323f60b55`, pair target 256, 90s solver / 180s outer limit): finished degree 2 and degree 3, then hit `INCOMPLETE_TIMEOUT` during degree-4 matrix construction after 82.064466 CPU / 90.231897 wall seconds. Basis empty, no marker, no count.
- **`exact_msolve_full_prime29_pairs16.*`** (byte-identical input, pair target 16): also timed out in degree-4 matrix construction after 69.161733 CPU / 90.259985 wall seconds, with no basis or count. Note that `-m` is a pair target rather than a strict cap; a [selector audit](exact_msolve_pair_batch_analysis.md) found an off-by-one in the upstream LCM tie loop that can exceed the target or split a tie group, though unselected pairs stay in the queue.
- **`exact_msolve_full_prime2_pairs16.*`** (same equations over F2): built a degree-4 matrix of 23,221 rows by 3,337,853 columns and found 17 new polynomials, then crashed growing the basis hash table under the 2-GiB cap (exponent-vector allocation error, signal 11, 69.641591 CPU / 80.636474 wall seconds; core dumps disabled). Basis empty, no count.

Source inspection traced that crash to post-LA promotion reserving and importing every nonpivot column into the basis hash. Because ordinary `core_f4` ignores the `-u` reset flag in this pinned version, toggling `-u` would not help.

To narrow that import, our [second build](exact_msolve_sparse_promotion_tools/README.md) imports only columns actually used by retained output rows. Its [independent review](exact_msolve_sparse_review_notes.md) verified 25 complete bases against both build 1 and Python Buchberger (including rounds that skip columns), plus 5,000 randomized mapping cases and 12 failure cases under ASan/UBSan.

Retrying the same F2 input with build 2 (`exact_msolve_full_prime2_sparse_promotion.*`, pair target 16, 2-GiB cap) imported fewer columns in early rounds but still ran out of memory growing the basis hash at degree 4 after 74.761294 CPU / 91.023190 wall seconds, leaving no basis or count.

## Dispersed elimination order and explicit F2 reduction

In natural cell order, the four unary linear equations pivot on cells `0, 1, 2, 3`, which all sit in the top T. Adding `--pivot-order` puts cells `0, 81, 90, 99` first so every T contains at most one pivot cell.

The [independent ordering audit](exact_parity_math_pivot_audit.md) parses generated F2 and F29 inputs, reverses the permutation, and matches every polynomial against both the original input and fresh geometry. All 100 cubic domains and 80 moments remain (a ring isomorphism with divisor 1; metadata records the cell map, and any prefix extension variable stays last).

- **`exact_msolve_pivot_fiber_six.*`** (reordered nine-row fiber over F2): completed with quotient dimension 12 and divisor 2, confirming 6 boards.
- **`exact_msolve_full_prime2_pivot_order.*`** (unrestricted reordered F2, 2-GiB cap): finished a degree-4 matrix of 45,045 by 2,656,383 (importing 1,985,794 new monomials), then crashed growing the basis hash after the next degree-4 matrix (44,435 by 2,663,283), exiting with signal 11 after 66.809504 CPU / 91.955289 wall seconds and no basis or count.

Alternatively, `--prime 2 --ternary-reduced all` substitutes out those four pivot variables explicitly, yielding 96 free cubic domains, 72 nonzero reduced moments, and 4 substituted pivot domains (172 generators; the `representatives` variant keeps 36 moments and 136 generators). Both have the full labeled count as quotient dimension (divisor 1). The [fresh geometric audit](exact_parity_math_reduced_input_audit.json) independently derived the substitutions and verified every emitted polynomial, including all four pivot cubics. Dropping pivot domains or making free variables Boolean would break the count. The reduced source JSON is pinned by SHA-256 separately from the emitted input hash, and conflicting options (such as odd characteristic or a fixed prefix) are rejected.

## Reserving only missing monomials

Build 2 still reserved slots for every referenced column even when a monomial already lived in the basis hash. Build 3 ([`exact_msolve_missing_promotion_tools`](exact_msolve_missing_promotion_tools/README.md), executable SHA-256 `1e2111b5e1ef28201f3b2da6bc727d4563569e96b3468ab241433e7d2238a202`) checks membership first and reserves space only for missing monomials, preserving existing IDs and ascending insertion order. Its [independent review](exact_msolve_missing_review_notes.md) verified 25 bases against build 2 and Python Buchberger, 5,000 sanitizer mapping/capacity cases, and 18 failure cases; the owner's separate 2,000-case harness tested real upstream lookup/rehash and 16 byte-identical basis comparisons (including the six-completion fiber).

Two full trials on build 3 under the 2-GiB cap:

- **`exact_msolve_full_prime2_pivot_missing.*`** (same reordered 100-variable F2 input): failed after 66.415649 CPU / 87.811644 wall seconds with no basis or count. The new diagnostic pinpointed the boundary: 2,078,104 existing entries plus 55,218 missing entries totaled 2,133,322, just over the 2,097,152 capacity, causing legacy doubling to request 4,194,304 entries and fail.
- **`exact_msolve_full_prime2_reduced_all_missing.*`** (audited 96-variable, 172-generator reduced input, SHA-256 `95363a4db10206ecc89852d09d93ac08d98311ea317af80c77f4488b72a3b66f`): shrank the first degree-4 matrix to 20,023 by 2,611,156, then hit the same doubling wall on the next round (2,080,795 existing plus 55,218 missing), failing after 69.012211 CPU / 99.694890 wall seconds with no basis or count.

## Separating exponent capacity from bucket capacity

Build 4 ([`exact_msolve_rounded_promotion_tools`](exact_msolve_rounded_promotion_tools/README.md), executable SHA-256 `cebd842aa617f09725a1f5429ebc822da238563f142b14993cccb85312d1874c`) rounds the required promotion exponent capacity (plus one spare slot) to a multiple of 65,536 while keeping bucket count as a separate power of two at least twice the exponent capacity. At the failing boundary above, 2,162,688 exponent slots replace 4,194,304, cutting 96-variable principal basis arrays from 904 MiB to 481.625 MiB.

Its [independent review](exact_msolve_rounded_review_notes.md) verified 25 complete bases with tiny initial hash `-s4`, real reallocation/collision tests, all four allocation-failure stages, and overflow/boundary checks; the owner's separate compatibility harness verified legacy growth, copy, clean, reinit, secondary tables, and reset after non-power-of-two capacity, plus 16 byte-identical basis comparisons.

Retrying the reduced F2 input with build 4 (`exact_msolve_full_prime2_reduced_all_rounded.*`) cleared the old boundary and finished the second degree-4 round, then crashed inside linear algebra on the third matrix (26,569 by 2,626,958) after 89.876150 CPU / 91.511242 wall seconds with no basis or count.

Two bounded debugger replays (preserving the same input, executable, and 2-GiB cap) captured `R12 = 0`, `RSI = 0`, and fault address `0x18` on the first output-row write. Disassembly maps `R12` to the unchecked `malloc` at `src/neogb/la_ff_8.c:542` and the crash to line 548, confirming a null output-row allocation (the requested size was not captured; see the [source/disassembly report](exact_msolve_la_analysis.md)). Debugger artifacts carry status `DEBUG_ONLY_NO_COUNT` and are never treated as counts.

## Smaller batches and live progress

Running the same reduced input and build 4 with pair-batch target 1 (`exact_msolve_full_prime2_reduced_pairs1.*`) finished 24 rounds without crashing before hitting its 180-second solver wall limit during degree 4 (last completed matrix: 12,119 by 2,552,995; next header: 293 pending pairs). It ended as `INCOMPLETE_TIMEOUT` after 168.970484 CPU / 180.147790 wall seconds with no basis or count.

The adapter now streams stdout and stderr straight into a fresh, exclusively opened `.log` file without rewriting completed logs or weakening any completion gate (verified for live visibility, timeout retention, overwrite protection, and a real count-6 fixture).

A planned 300-second trial at 3 GiB **never started**: free memory fell from roughly 4 GiB to 2,788 MiB, below the 3.5-GiB preflight requirement, so no solver ran and no artifacts exist for it. All full trials up to this point used a 2-GiB cap.

## Complete cap split and ordered F29 trial

The 10 top-two-row cap orbits partition all 81 caps with weights summing to 81 (not uniformly 12). The [independent cap audit](exact_msolve_cap_split_notes.md) verified all 10 models in characteristics 2 and 29 and added a strict aggregation adapter (`0000` has 96 variables, 176 generators, divisor 1; the other 9 add `a` with divisor 2). None of the 10 caps is solved yet.

- **`exact_msolve_cap0000_prime2.*`** (input SHA-256 `4aa5a5354dd1596d4240992c8a078604beecee72808a2b66f9106aafea602900`, build 4, pivot order, pair target 16, 180s / 2 GiB): finished 12 rounds (last degree-4 matrix 34,368 by 2,575,926; next header degree 4 with 903 pending pairs), then hit `INCOMPLETE_TIMEOUT` after 158.440272 CPU / 180.242095 wall seconds with no basis or count. (This four-cell fiber is distinct from the completed nine-row fiber.)
- **`exact_msolve_full_prime29_pivot_rounded.*`** (input SHA-256 `699e6a81b2f4c1b113a448dc17e5b81f5962a365729204ae32802c857fd9944d`, build 4, 100 variables / 180 generators, divisor 1, pair target 16, 120s / 2 GiB): finished 5 rounds through degree 3 (last matrix 18,741 by 169,762; next header degree 4 with 341 pending pairs), then exited with signal 11 (`BACKEND_ERROR`) after 90.237675 CPU / 91.784131 wall seconds with no fault location, basis, or count.

## Serial F2 matrix kernel

Build 5 ([`exact_msolve_f2_bitset_tools`](exact_msolve_f2_bitset_tools/README.md), executable SHA-256 `78e65a3c746a036d12ac67d8c332a9afd2101746eee3b850d4a2ecb5e696f502`) uses exact bitset Gaussian elimination on the guarded serial F2 export path while keeping generic kernels everywhere else. Variables still use ordinary cubic domains, old sparse reducers are freed before materializing new sparse rows, and checked allocation failures exit cleanly. An early draft that assumed sorted sparse tails failed closed and is preserved separately.

Its [independent review](exact_msolve_f2_review_notes.md) verified 1,039 kernel matrices under ASan/UBSan, 19 allocation failures, 16 invalid inputs/modes, and 12 complete F2 ideals against build 4 and Python Buchberger, alongside separate owner integration and fallback tests.

On the reduced F2 input (`exact_msolve_full_prime2_bitset.*`, SHA-256 `95363a4db10206ecc89852d09d93ac08d98311ea317af80c77f4488b72a3b66f`, pair target 16, 180s / 2 GiB), build 5 finished the previously crashing 26,569-by-2,626,958 matrix (17 new rows, 16,626,336 sparse output terms). On the next matrix (19,153 by 2,615,528), it printed `MSOLVE_F2_BITSET_ERROR: allocation failed` and exited cleanly with code 1 (`BACKEND_ERROR`, no signal or timeout) after 133.624000 CPU / 145.619429 wall seconds, leaving no basis or count.

## Redundant exact histogram constraints

`--histogram-e2` appends four role elementary-symmetric quadratics and their four Frobenius partners to an unrestricted F2 model. The [independent proof/input audit](exact_elementary_review_notes.md) verified ideal equality via radicality of the cubic-domain quotient (unchanged quotient dimension and divisor; incompatible with fixed prefixes).

Running build 5 on the augmented 96-variable, 180-generator reduced input (`exact_msolve_full_prime2_elementary.*`, SHA-256 `4338b3f86b8738130edbfb788504de14be08c60ada263afeba3f9844b437dd90`, pair target 16, 180s / 2 GiB) finished 4 rounds through degree 3 (last matrix 913 by 151,212; next header degree 4, 345 pending pairs), then exited with signal 11 (`BACKEND_ERROR`) after 121.120406 CPU / 134.879057 wall seconds with no fault diagnostic, basis, or count.

All four trials in these two sections left empty `.basis` files, no `.leading.json`, no completion marker, and no count. Their wrappers report `OUTER_PROCESS_FINISHED` with exit code 1 (meaning the wrapper finished cleanly, not that the solver succeeded). Timings above are solver child user+system CPU and wall times. Everything is archived in the [consolidated audit](exact_msolve_current_trials_audit.json), reproducible via `exact_msolve_terminal_audit.py`.

## Invertible prefix coordinates

To eliminate huge expanded pivot cubics, the prefix-sum coordinate change permutes all 100 cells by role signature, takes prefix sums, and eliminates the four unary linear equations. The [independent source and adapter audit](exact_pivot_review_prefix_notes.md) verified the invertible linear maps, all 100 transformed cubic domains, 72 nonzero Fourier moments, 8 elementary equations, and 96 optional quartic field equations `y_i^4 + y_i`. Quotient dimension equals the full labeled count (divisor 1); free coordinates can be zero, so no blanket cubic domains apply to them.

The transformed nine-row validation fiber finished with quotient dimension 12 and divisor 2 (6 boards), independently recounted across all 358 polynomials. After the solver succeeded, the postprocessor threw an error on the auxiliary variable name `a`; recovery verified the `x1,...,x96,a` header and parsed with an `a`-to-`x97` alias without rerunning the solver. Only the solver's rounded times (3.14 CPU / 3.17 wall seconds) survived, and the original exception and metadata fixes are preserved.

Two 3-GiB unrestricted trials ran on build 5 with pair target 16 and 300s solver / 360s outer limits:

- **`exact_msolve_full_prime2_prefix_gray_3g.*`** (all moments, `e2`, and quartics: 96 variables, 276 generators, input SHA-256 `60a5280098df62e0607fd3762a6e501b2d6098609b772138bd08f4f7ef867311`): finished 29 timed rounds, including 4 at degree 5 (last completed matrix 42,033 by 753,562). The next degree-5 matrix (210,803 by 6,546,994) returned 9 rows (5,528,411 terms) needing 3,463,587 missing monomials on top of 1,462,002 existing entries. Promotion requested 4,980,736 exponent slots (up from 1,572,864) and 16,777,216 buckets, then exited with code 1 (`Error: cannot allocate promotion exponent data.`, `BACKEND_ERROR`) after 248.070159 CPU / 252.145026 wall seconds (outer wall 252.462974 seconds). Empty basis, no marker, no count.
- **`exact_msolve_full_prime2_prefix_gray_e4_3g.*`** (adding `--histogram-e4`, 4 ordinary quartics of 12,324 / 1,146 / 278 / 446 terms verified in the [independent e4 audit](exact_pivot_review_e4_notes.md); 96 variables, 280 generators, input SHA-256 `72b09d3e2df822ea72f09dd1876580e950642a5681177d7aa604e8f6a68d9081`): finished 30 timed rounds (last degree-5 matrix 43,637 by 891,323; next header degree 5, 17 selected pairs, 3,246 pending), then printed `Enlarging exponent vector for hash table failed` / `for esz = 8388608, segmentation fault will follow.` and exited with signal 11 (`BACKEND_ERROR`) after 199.883521 CPU / 203.774695 wall seconds (outer wall 204.275440 seconds). The log does not specify which hash table failed. Empty basis, no count.

Both 3-GiB runs are recorded in `exact_msolve_current_trials_audit.json`.

## Natural characteristic three and staged symbolic storage

Encoding the palette `0, 1, 2` directly over F3 forces all 81 pattern counts to equal 1 modulo 3; combined with nonnegativity and total sum 81, every count must equal 1. Signed prefix sums and four unary eliminations leave 96 free variables whose field-domain ideal is simply the 96 equations `x_i^3 - x_i`. The [F3 source and proof review](exact_f3_review_notes.md) verified all 76 remaining power moments, 4 optional redundant histogram cubics (`e3`), and backend preparation; quotient dimension equals the full count directly (divisor and multiplier 1).

Build 6 stages only genuinely missing symbolic exponent vectors before growing the basis table, frees the old symbolic arrays, and restores a small empty secondary table while preserving insertion order and borrowed data. Build 6b extends that gate to F3. Its [independent review](exact_msolve_staged_review_notes.md) verified 1,200 ASan/UBSan cases, allocation failures, complete bases against Python Buchberger, and the exact one-line F3 gate diff.

- **`exact_msolve_full_native3_e3_staged_3g.*`** (build 6b `9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a`, 96 variables / 176 generators, input SHA-256 `cb2497554585e51166b747cee0221efc3cf7f130f46b9084d7f2e9d3b760c105`, pair target 16, 3 GiB, 300s / 360s): completed 23 timed rounds and 7 symbolic stagings (no F2 bitset kernel used). After a 21,640-by-1,032,184 degree-5 matrix (13 new rows), staging packed 837,014 missing monomials in 162,380,910 exponent bytes and grew basis capacity to 1,769,472. On the next degree-5 batch (16 pairs, 2,776 pending), it printed `Enlarging exponent vector for hash table failed` / `for esz = 8388608, segmentation fault will follow.` and crashed with signal 11 (`BACKEND_ERROR`) after 198.575927 CPU / 202.796805 wall seconds (outer wall 203.698359 seconds). Empty basis, no count (`exact_f3_terminal_review_results.json`).

Next, we factored out global color translation while keeping the independent apex-color field variable in the ideal (95 coupled normalized coordinates plus 1 independent F3 apex variable; quotient dimension still equals the full count, see [F3 review](exact_f3_review_notes.md)). We also built executable 7 (`a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a`), which reserves symbolic row capacity through the checked rounded allocator ([symbolic-reservation review](exact_msolve_symbolic_review_notes.md)).

- **`exact_msolve_full_native3_translation_e3_symbolic_3g.*`** (translated input SHA-256 `44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5`, build 7, pair target 16, 3 GiB, preflight 4,424 MiB available vs. 3,584 MiB required, 300s / 360s): finished 25 timed rounds (last degree-5 matrix 29,856 by 1,395,306; next header 16 pairs, 3,120 pending), 121 symbolic reservations (last request 3,604,480 slots rounded from 3,578,597 with spare), and 7 stagings, then hit `INCOMPLETE_TIMEOUT` at 247.204902 CPU / 300.256586 wall seconds (outer wall 301.456276 seconds, no solver exit code or error diagnostic). Empty basis, no count (`exact_f3_translation_terminal_review_results.json`).

## Minimum-fill native-F3 trials at 3 and 4 GiB

Build 7 (`a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a`) then ran the unrestricted 96-variable, 176-generator minimum-fill F3 input (`b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`, apex variable retained, divisor and multiplier 1) with 900s child / 960s outer limits:

- **3 GiB (`exact_f3_order_terminal_review_results.json`)**: `BACKEND_ERROR`, exit 1, after 285.469678 CPU / 328.585865 child wall seconds. Last completed degree-5 matrix: 17,439 by 3,200,323. The next checked symbolic reserve failed requesting 5,505,024 slots (up from 5,177,344).
- **4 GiB (`exact_f3_order_terminal_review_4g_results.json`)**: preflight 4,824 MiB available vs. 4,608 MiB required; `BACKEND_ERROR`, exit 1, after 331.312459 CPU / 351.842617 child wall seconds (outer wall 353.476518 seconds, process-tree CPU 333.052073 seconds). Completed 22 timed rounds (last degree-5 matrix 32,889 by 3,894,880). The next round needed 7,706,097 slots (5,097,099 existing plus a 2,608,997-term row plus 1 spare), requested 7,733,248 slots from 7,536,640 (16,777,216 buckets unchanged), and failed cleanly. Although the shared allocator's error text says "promotion exponent data", the preceding capacity line confirms it was a symbolic-table request.

Both independent terminal audits confirm empty basis files, zero completion markers, and no counts; both are archived in `exact_msolve_current_trials_audit.json`.

## Checked-byte exponent build review

Build 8 stores ordinary F3 exponent lanes in one checked byte (`uint8_t`) without reducing exponents modulo 256. Its scope requires explicit field domains for every variable, field-reduced remaining terms, at most 127 variables, and serial exact DRL export. The [independent review](exact_msolve_byte_review_notes.md) passed executable `63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76` across 20 ideals (80 native exports matching Python Buchberger and exhaustive enumeration), 34 fail-closed rejections, an ASan+UBSan arithmetic harness, and a source-only raw-guard check on the full minimum-fill input.

## Remaining color-reversal symmetry

The native-F3 adapter offers two mutually exclusive, separately audited options (both requiring `--prime 3 --ternary-native-field --native-e3 --native-translation` and compatible with `--native-order minimum-fill`):

- `--native-sign`: adds a quintic sign selector while keeping independent offset `a` and sign `s` variables (97 variables, 179 generators; quotient dimension directly equals the full labeled count).
- `--native-sign-branch K` (`K = 0, 1, 2, 3`): replaces the quintic with sparse linear branch constraints, keeping both finite factors; summing all four branch dimensions gives the full count. Adding `--native-branch-elimination` substitutes out solved canonical coordinates, leaving 96, 95, 94, or 93 variables depending on `K` (same branch count, not a separate summand; original colors reconstruct via `z = a + s * d` with degree-at-most-2 polynomials and no external factor of 2, 3, or 6).

The [sign-model review](exact_algorithms_sign_review.md) verified both inputs and the six-completion prefix. The [branch-adapter review](exact_algorithms_branch_adapter_review.md) verified all eight branch inputs and reproduced fixed-prefix branch counts `6, 0, 0, 0` across both counters. The [strict branch aggregator](exact_sign_branch_aggregate.md) demands one verified complete result per branch and rejects fixed prefixes, duplicate orders, incomplete runs, and missing branches.

Review caught one runner bug: a prepared `standard_basis_complete=False` flag was not flipped after successful parsing. The runner now updates both completion flags together, while the five small fixture JSONs keep verbatim `*.pre_flag_fix.json` copies plus metadata-only audit records (inputs, outputs, and counts untouched). Earlier full-run JSONs keep their original metadata and are audited directly against their basis exports.

## Eighth-build full trials (4 GiB and 3 GiB)

### Full minimum-fill F3 at 4 GiB (SIGSEGV)

Build 8 (`63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`) ran the unchanged minimum-fill input (`b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`, 96 variables / 176 generators, divisor and multiplier 1) at 4 GiB (preflight 4,942 MiB available vs. 4,608 MiB required; 900s child / 960s outer).

- **Outcome**: `BACKEND_ERROR`, solver return code -11 (SIGSEGV), wrapper exit 1, after 546.706832 child CPU / 564.328089 child wall seconds (outer wall 565.571819 seconds, process-tree CPU 548.501306 seconds).
- **Progress**: 24 timed rounds. Beyond build 7's 32,889-by-3,894,880 matrix, it finished degree-5 matrices of 57,321 by 5,384,334 (15 new rows) and 21,124 by 6,530,168 (16 new rows; promoted 2,101,181 monomials, basis capacity 7,929,856). Next batch selected 16 pairs (2,690 pending) with no matrix dimensions printed.
- **Last logged request**: symbolic reserve of 10,878,976 slots from 9,830,400 (6,439,449 existing + 4,424,268-term row + 1 spare = 10,863,718; 33,554,432 buckets unchanged). There is **no explicit allocation or arithmetic error** in the log, so the SIGSEGV cause is unconfirmed.
- **Audit**: `exact_f3_byte_terminal_review_results.json` (and `exact_msolve_current_trials_audit.json`) confirms empty basis, zero markers, and no count, preserving the original preparation-era metadata JSON.

### Full quintic-sign F3 at 4 GiB (SIGSEGV)

Build 8 (`63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`) ran the quintic-sign input (`14247d0e4cfaff8636e99852902816d8d0ab97de47ada08cb2e40fa7576e71cf`, 97 variables / 179 generators, offset and sign retained, divisor and multiplier 1) at 4 GiB (preflight 4,704 MiB available vs. 4,608 MiB required; 900s / 960s).

- **Outcome**: `BACKEND_ERROR`, solver return code -11 (SIGSEGV), wrapper exit 1, after 567.581942 child CPU / 598.196531 child wall seconds (outer wall 598.320039 seconds, process-tree CPU 568.314047 seconds).
- **Progress**: 24 timed rounds, ending with the same 21,124-by-6,530,168 degree-5 matrix (basis capacity 7,929,856), then 16 pairs selected (2,691 pending) and the same symbolic request (10,878,976 slots from 9,830,400 for 10,863,718 required; 33,554,432 buckets unchanged). No explicit allocation or arithmetic error appears, so the SIGSEGV cause remains unconfirmed.
- **Audit**: `exact_f3_sign_terminal_review.py` -> `exact_f3_sign_terminal_review_results.json` (and `exact_msolve_current_trials_audit.json`) confirms empty basis, zero markers, and no count. Optional stdout redirection to `/tmp` hit a quota error after both JSON reports were written completely; both reports parsed cleanly and later audits keep scratch files inside the workspace.

### Affine-eliminated branch 3 at 3 GiB (SIGSEGV)

Build 8 (`63e52125...`) ran the affine-eliminated branch-3 minimum-fill input (`f752d055d104dc6cd2d2599ce52c5931f1f6f8e082703eac42c978bfbbb033ae`, 93 variables / 174 generators, offset and sign at zero-based indices 91 and 92, divisor and multiplier 1; counts branch 3 only). An initial 4-GiB preflight deferred without starting a solver; the 3-GiB run launched with 4,499 MiB available vs. 3,584 MiB required (900s / 960s).

- **Outcome**: `BACKEND_ERROR`, solver return code -11 (SIGSEGV), wrapper exit 1, after 423.038078 child CPU / 452.188978 child wall seconds (outer wall 452.341549 seconds, process-tree CPU 423.616 seconds).
- **Progress**: 18 timed rounds; last degree-5 matrix 36,782 by 4,085,322 (promoted 1,519,984 monomials, basis capacity 4,587,520). Next batch: 16 pairs selected (1,983 pending), last symbolic request 6,946,816 slots from 6,488,064 (6,881,670 required with spare; 16,777,216 buckets unchanged). No explicit error diagnostic; SIGSEGV cause unconfirmed.
- **Audit**: `exact_f3_branch3_terminal_review_3g_results.json` (and `exact_msolve_current_trials_audit.json`) confirms empty basis, zero markers, and **null (not zero)** branch and full counts. Full-count divisibility and lower-bound checks apply only to the sum of all four branches.

## Reset-option source finding

The [reset-option review](exact_msolve_reset_review.md) confirmed that build 8's ordinary F3 export path never calls `reset_hash_table`. Flags `-u1` and `-u5` are parsed and printed, but the function is only called in an excluded saturation/tracing routine. Eighteen tiny `-g 1` / `-g 2` comparisons (including the six-completion prefix) gave byte-identical bases and identical allocation logs across `-u0`, `-u1`, and `-u5`. Even if invoked, `reset_hash_table` keeps capacity and allocates a temporary second same-size exponent slab and pointer array, so it cannot be assumed to save memory.

## Affine-eliminated branch 3 at 4 GiB (child timeout)

After bounded memory checks of 4,492, 4,546, and 5,138 MiB (earlier deferred 4-GiB preflights stay separate), `exact_msolve_branch3_eliminated_minfill_byte_4g_waited.*` launched on the same branch-3 input (`f752d055d104dc6cd2d2599ce52c5931f1f6f8e082703eac42c978bfbbb033ae`, 93 variables / 174 generators) and build 8 (`63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`), clearing the 4,608-MiB requirement.

- **Outcome**: `INCOMPLETE_TIMEOUT` at the 900-second child limit (576.156232 child CPU / 900.292436 child wall seconds; wrapper exited 1 after 900.434608 seconds wall and 576.993553 seconds process-tree CPU without hitting the 960s outer cap; no normal solver return code).
- **Progress**: 19 timed rounds, completing one more degree-5 matrix than the 3-GiB run: 42,571 by 5,264,659 (promoted 1,102,046 monomials, basis capacity 5,701,632). Next batch: 16 pairs selected (2,197 pending), last symbolic request 8,912,896 slots from 8,847,360 (5,510,079 existing + 3,353,155-term row + 1 spare = 8,863,235; 33,554,432 buckets unchanged). No allocation or arithmetic error appeared in the log.
- **Audit**: `exact_f3_branch3_terminal_review_4g_results.json` (and `exact_msolve_current_trials_audit.json`) confirms empty basis, zero markers, and no count. **Both branch 3 and the full four-branch total remain unknown (not zero).**

## Reproduction

After completing the local setup and patched build, pass a **fresh** output prefix (existing artifacts are never overwritten):

```sh
python3 experiments/exact_algebra_backend_guarded.py --backend msolve \
  --output experiments/exact_msolve_full_prime2_reduced_fresh \
  --outer-seconds 240 --outer-memory-mb 2048 -- \
  --prime 2 --ternary-reduced all --seconds 180 --memory-mb 2048 --max-pairs 16 \
  --executable experiments/exact_msolve_rounded_promotion_tools/msolve \
  --library-dir experiments/exact_algebra_backend_root/usr/lib \
  --require-export-marker
```

`-m` sets the batch target of critical pairs per matrix without dropping pairs from the ideal. A timeout or allocation error never implies zero solutions, and all 10 cap fibers in the symmetry manifest also remain uncounted.
