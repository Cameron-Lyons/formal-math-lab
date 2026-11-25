# Seventh preserved msolve build: symbolic row reservations

The candidate is `msolve`, SHA-256 `a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a`. It is based on pinned upstream v0.11.0 commit `cc044551f8e202d00691990fd3fd0b1226a88ea2` and the six previous preserved patches, including the separate F3 staging gate. `source.json` records the archive, predecessor patch, modified source, compiler, library, executable hashes and build commands. `symbolic-row-reserve.patch` is the complete change from frozen 6b; its SHA-256 is `11af8d44ef40a0fc51e91bdf24bed6f666b1d6870b2799020a558d4dcbdbf682`. No prior executable or source tree was changed.

The change addresses the measured pre-linear-algebra symbolic growth failure in `../exact_msolve_full_native3_e3_staged_3g.log`. That trial finished a 21,640-by-1,032,184 degree-five matrix and promoted 837,014 new monomials successfully, then the next symbolic construction failed when legacy growth requested exponent capacity 8,388,608. The log does not contain the failed row's length or actual symbolic load. This build logs both before every newly guarded capacity request. No full-board trial was run for this build, and no unrestricted count is claimed.

## Scope and invariants

Only three ordinary call sites in `src/neogb/symbol.c` change: the upper and lower selected-pair rows in `select_spairs_by_minimal_degree`, and a found reducer in `find_multiplied_reducer`. Each calls `reserve_symbolic_row_capacity` immediately before the unchanged `multiplied_poly_to_matrix_row` constructor. Other constructors and the generic `enlarge_hash_table` are unchanged.

The helper is active only for characteristic 2 or 3, exact sparse LA option 2, one thread, no trace, no normal-form mode, no final interreduction, no elimination block, and requested basis export. This is the same gate as 6b's consumable symbolic-table path. Active calls require `md->ht == sht`. Every other supported mode returns without changing the table.

For a source row of length L and next free entry E, at most L new monomials are inserted. Reserving at least E+L+1 entries ensures the legacy constructor's `while (eld+L >= esz)` test is false and leaves one spare even if every source term is new. Multiplication, coefficients, source-row ordering, symbolic IDs and the pending pair set are untouched. Repeated terms may reserve more space than used; this remains a conservative bound.

The existing checked promotion allocator is refactored into `reserve_hash_table_checked`, parameterized only by rounding quantum and diagnostic context. Its original wrapper still uses quantum 65,536 and context PROMOTION. Symbolic reservations use the next power of two below or at 65,536, then round upward to a multiple of 65,536. Probing buckets remain powers of two with at least twice the exponent capacity. Maximum entries 2^30 and buckets 2^31, checked size arithmetic and allocation failures retain the previous fail-nonzero behavior. The original error-message wording refers to promotion because the shared allocator is preserved; structured request diagnostics distinguish the actual context.

Reallocation copies all live `hd` entries, including `idx` markers, and reconstructs every exponent pointer. If the bucket count changes, existing monomial IDs are rehashed without reinsertion or ID reassignment. The three call sites copy the multiplier into a stack vector first. In `find_multiplied_reducer`, the old symbolic exponent pointer is never read after reserve; `hdm` is a value copy, and subsequent metadata access reloads through `sht`. Basis pointers are unaffected because basis and symbolic arrays are distinct.

Post-LA compaction now accepts a non-power-of-two exponent capacity when it is at least 2,048. It still requires a power-of-two bucket count, sufficient bucket and exponent bounds, the full live ID/column bijection, and the existing support checks. Compaction treats exponent capacity only as an array bound, never as a bit mask; the ascending-old-ID packing proof is unchanged. Such a table always restores to capacity 2,048 and 4,096 buckets. Smaller old capacities still must be powers of two. Borrowed random hashes, divisibility masks and scalar metadata remain untouched.

## Diagnostics and memory interpretation

At each guarded symbolic growth, verbosity 2 emits:

```
MSOLVE_SYMBOLIC_ROW_RESERVE old_load=E row_length=L required_with_spare=R requested_capacity=C
MSOLVE_SYMBOLIC_CAPACITY_REQUEST required_with_spare=R exponent_old=... exponent_new=C buckets_old=... buckets_new=...
```

Here R=E+L+1. These are actual request values, not a prediction of subsequent matrix size.

For the previous 96-variable model, each exponent vector occupies 97 uint16 entries, or 194 bytes. Principal symbolic storage is `capacity*(194+8+16)+bucket_count*4` bytes on this build. At the observed old capacity 4,194,304, that is 904 MiB. Legacy doubling requests 8,388,608 entries, or 1,808 MiB. The smallest possible 64K-rounded next capacity is 4,259,840, with 16,777,216 buckets, or 949.625 MiB. This last value is a best-case allocation calculation, not an observed needed target: the source polynomial may require several increments. The previously logged retained-support maximum 848,810 bounds a single existing output row; conditional on that and the initial input's smaller rows, the next request is at most 5,046,272 entries, or 1,113.125 MiB. These estimates apply to the previous input and do not predict a changed model's matrix sizes.

Repeated smaller growth can add rehash/reallocation work and transient copy requirements. Later symbolic matrices, basis promotion or linear algebra may still exhaust memory. The change removes excess geometric allocation at these three sites; it provides no completion or speed guarantee.

## Validation

`validation.json` contains 24 completed g1/g2 export comparisons against frozen 6b, byte-identical in every case, with strict exit/error/completion-marker checks. The fixtures cover characteristic 2 and 3 ordinary cubic domains, mixed ideals, unit and positive-dimensional ideals, and the natural-F3 known six-completion board fiber. Each finite g1 result agrees with both independent Python integer staircase counters, including exact quotient 6 for the board fiber. Logs record 56 actual symbolic reserve events and two F3 staging events. Total process CPU across the 48 solver invocations was approximately 1.015 seconds; each had a 30-second child wall guard and 2-GiB address-space limit. No whole-board input was solved.

`mode_validation.json` contains four completed full-basis comparisons for field 5, two threads, LA option 1 and an elimination block. Each matches frozen 6b, with no new symbolic reserve, F2 bitset, or staging event.

`helper_check.py/.c/.json` extracts the actual upstream lookup, insertion, row construction, legacy growth, copy, reset/reinsert and clean/reinitialize implementations, plus the candidate checked reserve and staged promotion. Only divisibility-mask and timing functions are stubs. ASan+UBSan checks pass:

- 49 previous rotation/collision/promotion cases, including zero-missing and reused support.
- Four 30,000-term actual row constructions at initial symbolic load 120,001, across F2/F3 and translated/untranslated supports. Candidate capacity 196,608 replaces legacy 262,144, preserving every live vector, ID, row support and coefficient metadata.
- Each large case subsequently stages the non-power table with reversed column order, matches baseline promoted IDs, then passes clean, insertion, lookup, legacy growth, copy, reinitialize and reset/reinsert.
- Eight disabled gate cases, seven exact/geometric/64K capacity boundaries, and all four shared allocator failures, each exiting nonzero before completion.

Independent review passed on the same frozen source and executable: [helper review](../exact_msolve_symbolic_review_results.json) and [basis review](../exact_msolve_symbolic_basis_review_results.json). The reviewer exercised 1,200 cases including 17 non-power stages, eight row boundaries, eight mode gates, ten promotion plus four row allocation failures, 22 rejected layout/reserve cases and three large arithmetic plans. Twenty-four distinct F2/F3 ideals produced 48 completed g2 exports, byte-identical to 6b and equal to an independent Python Buchberger basis; the cases exercised 22 F2 and 24 F3 symbolic reservations and three staging rounds in each characteristic. This independently verifies the implementation; it does not establish completion of an unrestricted board count.

## Reproduction

In a fresh output directory, run `prepare.py` then `build.py`; preparation refuses to replace an existing checkout. The archive and predecessor patches remain local and hash-checked. Build flags are `-O2 -g0`, static project libraries, no OpenMP, with the previously extracted local dependencies in `../exact_algebra_backend_root/usr`. Run `helper_check.py`, `validate.py` and `mode_validation.py` in a fresh artifact directory to avoid replacing recorded runs. Solver tests enforce resource limits; compilation is single-process.
