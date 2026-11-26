# Serial exact F2 matrix kernel

This fifth preserved build replaces one ordinary characteristic-2 F4 linear-algebra path with exact XOR reduction. It leaves the input ideal, monomial ordering, boundary coefficient arrays, hash tables, pair selection, final reduction, and export-completion protocol untouched. It adds no Boolean identities: a domain `x^3 + 1` still has quotient dimension 3 over F2.

The goal is to cut the transient matrix memory that triggered the earlier full run's confirmed null output-row allocation. No full board solve was run for this build or its validation.

## Pinned build

- Upstream: `algebraic-solving/msolve`, tag `v0.11.0`, commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`
- Original archive SHA-256: `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`
- Four predecessor patches and hashes: recorded in `source.json` (all four prior source trees, binaries, and results remain untouched)
- New patch: `serial-f2-bitset.patch`, SHA-256 `3868e06ffa3fba3f1ff30aab9693070489fdc533a683df6e8e6d8ad7c92b3a8b` (adds `src/neogb/la_ff_2_bitset.c` and edits only the dispatch in `exact_sparse_linear_algebra_ff_8` in `src/neogb/la_ff_8.c`)
- Frozen executable `msolve` SHA-256: `78e65a3c746a036d12ac67d8c332a9afd2101746eee3b850d4a2ecb5e696f502`
- New kernel source SHA-256: `194f90bf81adf33cbc006933367056cffce4c2be2fa9210886596b89593928eb`
- Modified caller source SHA-256: `1f949f50b071ab0a249d225012d14c2b996f4f21a5acac25ad3ed9b195f8cffc`

The build uses `CFLAGS=-O2 -g0`, local headers and libraries in `../exact_algebra_backend_root/usr`, and the same commands as the fourth build (`./autogen.sh`, `./configure --disable-shared --enable-static --disable-openmp`, `make -j1`). Exact paths, environment, commands, and timings are in `source.json`. No system install is needed.

## Scope and row invariants

Dispatch enters the bitset kernel only when every condition holds:

- `fc == 2`, `laopt == 2`, `nthrds == 1`
- `trace_level == NO_TRACER`, `nf == 0`
- no final-reduction step, no elimination block, and `print_gb > 0`

All other modes fall back to the unchanged generic kernel. The new routine repeats these guards and checks the matrix layout: `nru == ncl`, old pivot row `i` leads at column `i`, and every sparse input row has nonempty support, a valid coefficient index, coefficient 1 at every entry, no duplicate columns, and all tail columns strictly greater than the leading column. Tail columns may appear in any order, because the upstream converter partitions columns into known and unknown pivots without sorting row tails (`convert.c`, comment starting at line 403 in the fourth source).

An earlier draft required sorted tails and rejected the first integrated root-sum test cleanly before writing any completion marker. Its binary and logs are saved in `msolve-initial-order-check` and `initial_order_check/`. The frozen build fixes that check, and no failed run was treated as a count.

## Why reduction is exact

Over F2, addition and subtraction are XOR and every nonzero coefficient is 1, so one bit at column `c` encodes the exact coefficient of column `c`.

Known upper rows stay sparse. For each lower row in order, the routine copies its support into a zeroed bitset and scans set bits from left to right. A known old pivot toggles its sparse support; a previously found new pivot applies a wordwise XOR. Because reducers have no entries left of their pivot, applying one never changes an earlier column. Columns without a pivot stay set. When the scan finishes, either the row is zero or its leftmost set bit becomes a new pivot. Each step only adds rows already in the row space, so adding a nonzero remainder preserves the row space and raises rank by 1. No random choices or incomplete pivot tests are used.

All new pivots are zero on the old pivot columns. Sorting them by decreasing leading column and clearing every larger pivot yields the unique reduced row basis of the residual right-block space. Because already interreduced rows have zeros at every other larger pivot, later XORs never reintroduce a cleared pivot. Outputs have sorted supports, all coefficients equal to 1, and decreasing leading-column order, matching the generic serial kernel. `BINDEX`, `MULT`, and the original lower-row coefficient slot stay intact; `DEG` starts at 0 and is filled in by the existing matrix-to-basis converter from the leading monomial.

The resulting polynomials match the generic serial kernel and pass into unchanged basis insertion and pair-update code. Final basis interreduction also stays on the generic kernel.

## Ownership and allocation audit

| Object | Handling |
| --- | --- |
| Input upper/lower coefficient arrays | Borrowed from `bs`/`tbr`; read for validation, never modified or freed. |
| Input lower sparse row arrays | Copied into the workspace, then freed once and their `mat->tr` slots cleared. |
| Input upper sparse row arrays | Used during forward reduction, then freed once and their `mat->rr` slots cleared. |
| Packed workspace and new pivots | Owned locally. A nonzero workspace becomes a pivot and a fresh zeroed workspace is allocated. All are freed before return. |
| Matrix pointer containers | Old `mat->tr` and `mat->cf_8` containers are freed; new ones are sized to the output count and lower-row count. `mat->rr` stays for `clear_matrix`. |
| Output sparse rows and coefficient arrays | Fresh standard allocations. Ownership transfers via unchanged matrix-to-basis conversion; `clear_matrix` later frees only pointer containers. |

All obsolete upper sparse rows are freed before any new sparse output row is allocated. New pivots stay packed through forward elimination and interreduction, and sparse output is materialized once. No full-column pointer table is allocated. Every new allocation checks size arithmetic and return values, exiting nonzero on failure well before the export patch writes its completion marker.

Note that the generic kernel also frees each old self-row before replacing it during interreduction, so this patch does not claim the generic path keeps two full sparse output sets alive together. Instead, it prevents the first sparse output set from coexisting with all old reducer rows and avoids repeated sparse materialization.

## Memory scope

At the measured matrix width of 2,626,958 columns:

- One packed bitset uses 328,376 bytes (0.3132 MiB), versus 21,015,664 bytes (20.0421 MiB) for a generic `int64_t` workspace.
- Skipping the generic full-column pivot-pointer table saves another 20.0421 MiB.
- For illustration, 17 packed new rows take 5.3238 MiB and 33 take 10.3344 MiB (these illustrate scale rather than measuring the failed allocation or a new full run).
- A sparse output row with `k` terms takes about `5*k + 24` bytes (4-byte column index, 1-byte coefficient, plus 6 metadata words), so a bitset wins once support exceeds roughly 2.5% of columns. Old rows stay sparse because the measured matrix density was about 0.13%.

The persistent sparse basis, both monomial hash tables, and the generic final-reduction path remain. This build does not guarantee that a full run fits in 2 GiB or finishes quickly. Searching the small new-pivot list linearly keeps the code simple, and its CPU cost on very large runs is untested.

## Validation

- `validate.py` and `validation.json`: 18 completed `-g 1` / `-g 2` comparisons, all byte-identical to the fourth build. Covers 7 small ordinary F2 ideals, the known six-completion F2 prefix, and the same prefix over F29 (old-kernel regression). Both bigint counters give quotient dimension 12 for each prefix (6 boards after dividing by extension degree 2). Single and paired F2 cubic domains keep dimensions 3 and 9, the three-root sum keeps dimension 6, and positive-dimensional input is rejected. Diagnostics show the mixed-chain and F2 prefix cases enter the bitset path while F29 does not.
- `mode_validation.py` and `mode_validation.json`: 4 completed full-basis comparisons for LA option 1, thread count 2, an elimination block, and characteristic 5. All match the fourth build byte-for-byte with no bitset diagnostic. Because OpenMP is disabled, the thread-count case checks dispatch rather than parallel execution.

Independent review passed on the frozen executable and kernel hashes:

- `../exact_msolve_f2_matrix_review_results.json`: ASan/UBSan harness compiling the actual C source against a Python oracle on 1,039 matrices and 11,594 output pivots (including 961 unsorted-tail cases and 57 zero-output cases). Verified ownership, original coefficient slots, metadata, 19 injected allocation failures, and 16 invalid-mode/input rejections, with zero sanitizer findings.
- `../exact_msolve_f2_basis_review_results.json`: 12 complete F2 ideals producing 24 byte-identical baseline/candidate bases that match a Python Buchberger oracle, exercising 33 bitset rounds (including a cubic of dimension 27 and a nonradical ideal of multiplicity 6).

The reviewer also preserved an early baseline failure under a 1-GiB address-space cap; rerunning at the standard 2-GiB cap succeeded, confirming it was a resource limit rather than a regression. No full T-board run was executed during validation.
