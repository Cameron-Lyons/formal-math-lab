# Seventh preserved msolve build: symbolic row reservations

- Executable `msolve` SHA-256: `a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a`
- Upstream base: pinned msolve `v0.11.0`, commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`, plus the six earlier patches (including the F3 staging gate)
- Incremental patch from build 6b: `symbolic-row-reserve.patch`, SHA-256 `11af8d44ef40a0fc51e91bdf24bed6f666b1d6870b2799020a558d4dcbdbf682`
- Full manifest: `source.json` (archive, predecessor patches, modified files, compiler, library, and executable hashes, plus build commands)

All prior binaries and source trees stay untouched.

This build targets the pre-linear-algebra symbolic growth failure in `../exact_msolve_full_native3_e3_staged_3g.log`, where legacy growth failed requesting 8,388,608 exponent slots right after a 21,640-by-1,032,184 degree-5 matrix promoted 837,014 new monomials. Because that log did not report the failing row length or symbolic load, this build logs both before every guarded request. No full-board trial was run for this build.

## Scope and invariants

Only three ordinary call sites in `src/neogb/symbol.c` change: upper and lower selected-pair rows in `select_spairs_by_minimal_degree`, and matched reducers in `find_multiplied_reducer`. Each calls `reserve_symbolic_row_capacity` right before the unchanged `multiplied_poly_to_matrix_row`. Other constructors and generic `enlarge_hash_table` stay untouched.

The helper runs only under build 6b's exact mode gate: characteristic 2 or 3, exact sparse LA option 2, single thread, no trace, no normal form, no final interreduction, no elimination block, basis export requested, and `md->ht == sht`. All other modes return immediately without modifying the table.

For a source row of length `L` and next free entry `E`, multiplying can insert at most `L` new monomials. Reserving at least `E + L + 1` entries prevents the legacy `while (eld + L >= esz)` loop from firing and leaves one spare slot even if every term is new. Multiplication, coefficients, row order, symbolic IDs, and pending pairs stay unchanged. Duplicate terms can still cause over-reservation, so `E + L + 1` is a conservative upper bound.

The checked promotion allocator is factored into `reserve_hash_table_checked`, parameterized by rounding quantum and diagnostic label:

- Promotion keeps quantum 65,536 and context `PROMOTION`.
- Symbolic reservations grow by powers of two up to 65,536, then round up to multiples of 65,536.
- Buckets stay powers of two at least twice the exponent capacity.
- Maximum limits (`2^30` entries, `2^31` buckets), overflow checks, and nonzero exit on allocation failure stay identical. Because the allocator is shared, its generic error message still says "promotion", while the structured request line identifies the actual context.

Reallocation preserves all live `hd` records (including `idx`), rebuilds every exponent pointer, and rehashes existing IDs without reassigning them when buckets grow. At all three sites, the multiplier vector is already copied to the stack before reservation; in `find_multiplied_reducer`, `hdm` is copied by value, no old symbolic exponent pointer is read afterwards, and later metadata reads reload through `sht`. Basis pointers stay unaffected because basis and symbolic tables are separate.

Post-LA compaction now allows non-power-of-two symbolic exponent capacities of at least 2,048 (restoring them to 2,048 slots and 4,096 buckets), while keeping power-of-two bucket checks, the full ID/column bijection, and power-of-two validation for smaller tables. Borrowed weights, divisibility masks, and scalar metadata stay untouched.

## Diagnostics and memory interpretation

Each guarded symbolic growth prints at verbosity 2:

```
MSOLVE_SYMBOLIC_ROW_RESERVE old_load=E row_length=L required_with_spare=R requested_capacity=C
MSOLVE_SYMBOLIC_CAPACITY_REQUEST required_with_spare=R exponent_old=... exponent_new=C buckets_old=... buckets_new=...
```

Here `R = E + L + 1`. These lines show actual capacity requests, not predictions of final matrix size.

For the 96-variable model, each exponent vector has 97 `uint16_t` entries (194 bytes), so principal symbolic arrays take `capacity * (194 + 8 + 16) + bucket_count * 4` bytes:

- Old capacity 4,194,304: 904 MiB
- Legacy doubling (8,388,608 entries): 1,808 MiB
- Smallest 64K-rounded step (4,259,840 entries, 16,777,216 buckets): 949.625 MiB (best-case single step; a long row can require more increments)
- Bounded by the previously logged maximum retained row of 848,810 terms: at most 5,046,272 entries (1,113.125 MiB)

Smaller growth steps can add extra rehashes and temporary reallocation copies, and later matrices, promotion, or linear algebra can still hit memory limits. This change trims excess doubling at these three sites without guaranteeing speed or completion.

## Validation

- `validation.json`: 24 completed `-g 1` / `-g 2` comparisons against build 6b, all byte-identical with strict exit, error, and completion-marker checks. Covers F2 and F3 cubic domains, mixed ideals, unit and positive-dimensional ideals, and the natural-F3 nine-row six-completion fiber (exact quotient 6 across both Python bigint counters). Exercised 56 symbolic reservations and 2 F3 stagings (~1.015 seconds total CPU across 48 runs, 30s child wall / 2 GiB cap). No full board was solved.
- `mode_validation.json`: 4 completed full-basis comparisons (characteristic 5, 2 threads, LA option 1, elimination block), all matching build 6b with zero symbolic reserve, bitset, or staging events.
- `helper_check.py`, `.c`, `.json`: ASan+UBSan harness running actual upstream lookup, insertion, row construction, legacy growth, copy, reset/reinsert, and clean/reinit plus the new reserve and staging helpers (stubbing only divisibility masks and timers):
  - All 49 prior rotation/collision/promotion cases (including zero-missing and reused supports).
  - Four 30,000-term row constructions at load 120,001 across F2/F3 and translated/untranslated supports: capacity 196,608 replaces legacy 262,144 with identical vectors, IDs, supports, and coefficient metadata, followed by reversed-column staging and clean/insert/lookup/legacy growth/copy/reinit/reset checks.
  - 8 disabled-gate cases, 7 exact/geometric/64K boundaries, and all 4 shared allocator failures exiting nonzero cleanly.

Independent review passed on the same frozen source and binary ([helper review](../exact_msolve_symbolic_review_results.json), [basis review](../exact_msolve_symbolic_basis_review_results.json)): 1,200 extracted-helper cases (17 non-power stages, 8 row boundaries, 8 mode gates, 10 promotion + 4 row allocation failures, 22 rejected layouts/reserves, 3 large arithmetic plans) plus 24 F2/F3 ideals producing 48 byte-identical `-g 2` exports matching Python Buchberger (22 F2 and 24 F3 symbolic reserves; 3 staging rounds each).

## Reproduction

Run `prepare.py` then `build.py` in a fresh output directory (`prepare.py` refuses to overwrite existing checkouts). The build uses `-O2 -g0`, static project libraries, no OpenMP, single-process `make`, and local dependencies in `../exact_algebra_backend_root/usr`. Run `helper_check.py`, `validate.py`, and `mode_validation.py` in a fresh artifact directory so saved runs stay intact.
