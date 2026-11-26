# Independent missing-only reservation review

Reviewed incremental patch: `exact_msolve_missing_promotion_tools/missing-column-reservation.patch`, SHA-256 `c0940b59cd8b6a62d22ee6a7072d6614a9532d82a3b16ca2403fe631fd8b9022`.
Reviewed executable SHA-256: `1e2111b5e1ef28201f3b2da6bc727d4563569e96b3468ab241433e7d2238a202`.

This patch builds on the audited retained-column promotion helper and keeps the same call-site restrictions.

## Lookup, mapping, and allocation semantics

Previously, the helper reserved a basis slot for every referenced column even when that monomial was already in the basis hash. The new helper looks up each referenced exponent vector first using the basis table's own random hash multipliers and full vector width. Because `is_contained_in_hash_table` returns three values (`1` for found, `0` for missing, and `-1` for lookup failure), the patch handles all three explicitly rather than treating the return code as a Boolean.

- Found monomials store their basis exponent-array ID in `hcm` and mark their support byte as `2`.
- Missing monomials keep their symbolic ID in `hcm` and keep their support byte as `1`.

The helper reserves space only for the missing count, then imports those entries in ascending column order. If the number actually inserted does not equal the missing count, the process exits with an error.

Cached existing IDs stay valid across basis-table growth because the upstream enlarger preserves array positions and reinserts the same IDs into the resized bucket array. The patch never caches a missing monomial's bucket slot or an exponent pointer across growth; it refetches missing vectors from the separate symbolic table during insertion. It also explicitly rejects aliased basis/symbolic tables and unequal exponent widths.

Existing IDs, row supports, coefficient links, and insertion order therefore match the prior selective build. Because matrix columns represent distinct symbolic monomials, all new entries are distinct, and the insertion-count check enforces that invariant. When every referenced monomial is already present, no growth runs even if the basis table is full, and per-insertion capacity checks block silent writes past reserved space.

Call-site guards stay unchanged: ordinary exact sparse F4, positive characteristic, no trace replay, no elimination block, and basis-export mode. Legacy, trace, saturation, and final-reduction callers still use the original wrapper, and no polynomial or linear-algebra math changes.

## Independent checks

We extracted the exact new helper and compiled it against an instrumented hash table under ASan and UBSan (`exact_msolve_missing_helper_check.py`, its generated C harness, and `exact_msolve_missing_helper_results.json`):

- 5,000 randomized support/mapping cases, verifying that capacity grows only enough for genuinely missing entries.
- A full-capacity, all-reused case that must not grow the table.
- 18 failure cases covering invalid rows/columns/hashes, mask-allocation failures, lookup errors, invalid existing IDs, aliased tables, unequal exponent widths, and insertion-count mismatches.

Because this harness uses an instrumented lookup and allocator, it checks the helper's logic rather than the upstream allocator itself. The build owner's separate 2,000-case harness in `exact_msolve_missing_promotion_tools/helper_check.json` exercises the actual upstream lookup, insertion, and enlargement routines with hash collisions, overlapping supports, and relocation.

All 25 independent small completed-basis comparisons passed against both the prior selective binary and an exact Python Buchberger implementation (5 systems across characteristics 2, 5, 29, 257, and 65537). The four-variable mixed chain skips unused columns, including a 2-of-6 import round, and all full reduced bases match byte-for-byte. Raw artifacts are under `exact_msolve_missing_review_runs/`, with hashes and results in `exact_msolve_missing_review_results.json`.

Reproduce the independent checks:

```sh
python experiments/exact_msolve_missing_helper_check.py
python experiments/exact_msolve_sparse_review.py --baseline experiments/exact_msolve_sparse_promotion_tools/msolve --candidate experiments/exact_msolve_missing_promotion_tools/msolve --artifact-prefix exact_msolve_missing_review
```

The upstream allocator's existing unchecked reallocation paths remain untouched, so any allocation crash still leaves a run incomplete and never implies a zero count. This review ran no full T-board solve and makes no claim that the full model fits within resource limits.
