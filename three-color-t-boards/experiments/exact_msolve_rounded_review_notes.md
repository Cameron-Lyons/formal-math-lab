# Independent rounded promotion-capacity review

Reviewed patch: `exact_msolve_rounded_promotion_tools/rounded-promotion-capacity.patch`, SHA-256 `d569538b42f58dbf7160621891918cddc9496347a8229f350350eb5977539461`.
Reviewed executable SHA-256: `cebd842aa617f09725a1f5429ebc822da238563f142b14993cccb85312d1874c`.

Compared to build 3, only the guarded promotion reserve helper changes; the upstream grower stays untouched.

## Arithmetic and memory review

The reserve helper computes `eld + missing + 1` (keeping one spare slot for exact-fill checks in later insertion code) and rounds up to a multiple of 65,536 exponent slots. Bucket capacity stays a power of two at least twice the exponent capacity. The helper rejects invalid layouts, capacities above `2^30` entries or `2^31` buckets (avoiding a legacy reinsertion path that narrows bucket count to 32 bits), and size products that would overflow platform allocation limits.

For the measured failing reservation:

```text
load                      2,080,795
missing                      55,218
required including spare  2,136,014
rounded exponent capacity 2,162,688
bucket capacity           8,388,608
```

Legacy doubling would have requested 4,194,304 exponent slots. Source inspection confirmed that exponent capacity is used only for linear array bounds and allocations, while power-of-two bit masking applies only to bucket indexing.

All four potential reallocations use checked temporary pointers, exiting nonzero on failure before any basis export can complete. The old exponent block pointer is saved before reallocating the pointer array; once the exponent slab moves, **every** `ev` pointer (including slot 0) is rebuilt. Existing metadata and entry positions stay intact. When buckets grow, the bucket array is cleared and all existing IDs are rehashed with the same probe sequence, keeping IDs and insertion order unchanged. New capacities are written to the table only after every step succeeds.

Shared arrays such as random hash multipliers and divisor masks never move. Copy, clean, and reset use the stored capacities directly, and legacy doubling keeps the power-of-two bucket count and bucket-to-entry ratio intact even after exponent capacity becomes a non-power-of-two multiple of 65,536. Existing limits and unchecked allocations in untouched legacy code stay as they were.

## Independent executable checks

`exact_msolve_rounded_capacity_check.py` extracts the exact reserve helper and tests it under ASan and UBSan (`exact_msolve_rounded_capacity_results.json`):

- 3 real reallocation and collision cases, including non-power-of-two capacity 196,608 and the unchanged-bucket branch, verifying rebuilt pointers, saved metadata/exponents, and collision-heavy lookups.
- Failure injection at all 4 reallocation sites, each exiting nonzero cleanly.
- 7 capacity plans covering the measured failure size, no-growth cases, exact-boundary rounding, and the upper bound (large plans intentionally fail at the first allocation rather than allocating gigabytes).
- 13 invalid-layout, limit, and overflow rejections, including 3 native harness tests that cap `SIZE_MAX` to exercise 32-bit allocation guards (modeling those guards without claiming a separate 32-bit binary).

All 25 small completed-basis comparisons passed with tiny initial hash size `-s4` (including 5 cases in characteristic 2). Exports match build 3 byte-for-byte and agree with an independent Python Buchberger solver, while logs record **10 actual rounded-growth events**. Results and hashes are in `exact_msolve_rounded_review_results.json` and raw files are in `exact_msolve_rounded_review_runs/`.

We also read the build owner's separate compatibility harness (`exact_msolve_rounded_promotion_tools/compatibility_check.json`) and reviewed its assertions. Starting from capacity 196,608, it tests upstream legacy growth to 393,216, copy, clean, reinitialization, secondary-table init and growth, reset/reinsertion (verifying renumbered vectors), and the exact-boundary spare slot in both normal and forced-collision modes, stubbing only divisibility masks and timers. Those results belong to the owner's harness rather than this review; patch and executable hashes were rechecked unchanged afterwards.

**Review complete: no correctness issues found in the guarded path.** Both independent checks and the owner's caller-compatibility tests support running a bounded full-input trial.

```sh
python experiments/exact_msolve_rounded_capacity_check.py
python experiments/exact_msolve_sparse_review.py --baseline experiments/exact_msolve_missing_promotion_tools/msolve --candidate experiments/exact_msolve_rounded_promotion_tools/msolve --artifact-prefix exact_msolve_rounded_review --initial-hash-log2 4
```

This review ran no full T-board solve. Any memory error, timeout, or incomplete export leaves the count unknown and never implies zero.
