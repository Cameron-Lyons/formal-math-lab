# Independent missing-only reservation review

Reviewed incremental patch:
`exact_msolve_missing_promotion_tools/missing-column-reservation.patch`,
SHA256 `c0940b59cd8b6a62d22ee6a7072d6614a9532d82a3b16ca2403fe631fd8b9022`.
Reviewed executable SHA256:
`1e2111b5e1ef28201f3b2da6bc727d4563569e96b3468ab241433e7d2238a202`.
This builds on the separately audited retained-column promotion and keeps its
call-site restrictions unchanged.

## Lookup, mapping, and allocation semantics

The earlier helper reserved a slot for every referenced monomial, including
those already in the basis. The new helper first looks up each referenced
exponent vector using the basis table's own random hash multipliers and full
exponent-vector width. The source routine
`is_contained_in_hash_table` returns three distinct states: one for an existing
entry, zero for a missing entry, and minus one for lookup failure. The patch
handles these explicitly; treating the result as a Boolean would be wrong.

For an existing monomial it stores the returned exponent-array entry ID in
`hcm` and marks the support byte as two. For a missing monomial the original
symbolic entry ID remains in `hcm` and the support byte stays one. It reserves
only the number marked missing, then imports those entries in ascending
column order. The number actually inserted must equal the number reserved as
missing; otherwise the process terminates with an error.

The cached existing IDs remain valid during basis-table enlargement: the
upstream allocator moves storage but preserves entry positions and reinserts
the same IDs into the resized bucket table. The patch never caches the bucket
index returned for a missing monomial, nor an exponent pointer across the
growth operation. Missing exponent vectors are fetched again from the
separate, unchanged symbolic table at insertion time. The patch explicitly
rejects aliased basis/symbolic tables and unequal exponent widths.

Existing IDs, row supports, coefficient associations, and retained insertion
order therefore agree with the prior selective implementation. New entries
are distinct because columns enumerate distinct symbolic monomials; the
insert-count postcondition also catches a violation of that invariant. An
all-reused set needs no growth even when the basis exponent array has no free
slots. Per-insertion capacity checks prevent silently consuming unreserved
storage.

The existing restrictions remain: ordinary exact sparse F4, positive
characteristic, no trace replay, no elimination block, and basis-export mode.
Legacy, trace, saturation, and final-reduction callers keep their old wrapper.
No polynomial or linear-algebra operation was changed.

## Independent checks

The exact new helper was extracted and compiled against an instrumented table
with address and undefined-behavior sanitizers. It passed:

- 5,000 randomized support/mapping cases, now also checking that capacity
  grows only as far as required by genuinely missing entries.
- A full-capacity, all-reused case that must not enlarge.
- Eighteen failure cases, including the earlier invalid-row/column/hash and
  mask-allocation cases plus lookup failure, invalid existing IDs, aliased
  tables, unequal exponent widths, and insertion-count disagreement.

Artifacts: `exact_msolve_missing_helper_check.py`, its generated C harness,
and `exact_msolve_missing_helper_results.json`. This independent harness uses
an instrumented lookup and allocator; it does not claim to implement the
upstream allocator.

The separate patch owner's actual-upstream-routine harness additionally
passed 2,000 cases with real lookup, insertion, and enlargement, including
hash collisions, overlapping existing supports, and relocation. Its results
are in `exact_msolve_missing_promotion_tools/helper_check.json`; those results
are attributed to that harness, not duplicated by this reviewer.

All 25 independent small completed-basis comparisons passed against both the
previous selective executable and a separate exact Python Buchberger
implementation. Five cases run at each of characteristics 2, 5, 29, 257, and
65537. The four-variable mixed chain genuinely skips columns, including a
two-of-six import round. Full reduced bases remain byte-identical. Inputs,
logs, and exports are under `exact_msolve_missing_review_runs/`; hashes and
results are in `exact_msolve_missing_review_results.json`.

Reproduce the independent checks with:

```sh
python experiments/exact_msolve_missing_helper_check.py
python experiments/exact_msolve_sparse_review.py --baseline experiments/exact_msolve_sparse_promotion_tools/msolve --candidate experiments/exact_msolve_missing_promotion_tools/msolve --artifact-prefix exact_msolve_missing_review
```

The upstream allocator's preexisting unsafe allocation-failure handling is
unchanged. A crash or failed allocation remains a failed/incomplete backend
run, never an exact zero count. This review starts no full T-board computation
and makes no claim that the full input will finish within its resource limit.
