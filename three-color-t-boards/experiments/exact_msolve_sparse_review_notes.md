# Independent retained-column promotion review

- Reviewed patch: `exact_msolve_sparse_promotion_tools/retained-column-promotion.patch`, SHA-256 `3955ca519da0b32a5e000792d7d36000d45a8971eea8fb56d1e793cd40a0edeb`
- Candidate executable SHA-256: `997199fc836584627dc1c6324fc2702a4d900f4cee84d4534acd89f29a068093`
- Previous export-only executable SHA-256 (unchanged): `2d3258dd099a34410b05eadd21dbb38db22b8be0962ab59115d01660652c355d`

## Source and semantic review

The original `switch_hcm_data_to_basis_hash_table` reserves and imports every column in the nonpivot block `[ncl, nc)` and is called only by sparse matrix-to-basis conversion. The new helper instead imports only the union of supports of retained output rows, tracked with a byte mask of length `ncr`.

It scans every term `mat->tr[i][OFFSET+j]` (`i < mat->np`, `j < row[LENGTH]`), covering full row supports rather than just pivots. It checks dimensions, nonempty row pointers and lengths, column bounds, and symbolic hashes, deduplicates referenced columns, reserves space for their union, and inserts them in ascending column order. Referenced entries of `hcm` become basis hash IDs while unused entries stay untouched.

Because subsequent conversion reads only terms inside retained rows, the exported polynomials stay exact: coefficient arrays, indices, term order, and basis-row order are unchanged. Existing basis IDs stay stable, keeping pending pairs valid. New IDs can shift numerically because unused monomials are omitted, which is safe on the ordinary path where every ID still resolves to its exact exponent vector.

Those numeric ID shifts are **not** safe for trace replay, which compares leading-monomial hash IDs directly across primes whose supports can differ. We flagged this before the patch was finalized, and the final build restricts selective import to `compute_new_elements` only when all five conditions hold:

```text
trace_level == NO_TRACER
laopt == 2
fc > 0
nev == 0
print_gb > 0
```

The old-signature wrapper still calls the all-column importer, so tracing, modular, saturation, and final-reduction paths stay untouched. On the ordinary path, the symbolic table and matrix are cleared right after conversion and rebuilt from scratch in the next round, so unused symbolic entries are never read as basis terms.

Mask-allocation errors and invariant violations exit nonzero cleanly. Upstream `enlarge_hash_table` still has unchecked `realloc` calls, so an out-of-memory error there can still crash with SIGSEGV; the backend marks any crash as failed/incomplete and never treats it as zero solutions.

## Independent executable checks

`exact_msolve_sparse_helper_check.py` extracts the new helper and compiles it against an instrumented minimal hash table under ASan and UBSan:

- 5,000 deterministic randomized cases with shared supports, reused basis entries, shuffled column maps, and varied row lengths.
- Confirms every referenced monomial maps properly, existing IDs and row metadata stay intact, unused columns stay untouched, and new insertions occur in ascending column order.
- 12 rejection cases covering invalid dimensions, row pointers/lengths, out-of-block columns, invalid symbolic hashes, and mask-allocation failure.

Because the harness stubs the hash allocator, it tests helper logic rather than upstream out-of-memory behavior.

`exact_msolve_sparse_review.py` checks 5 small systems (root sums, root products, a mixed cubic system, a quadratic cycle, and a four-variable mixed chain) across characteristics **2, 5, 29, 257, and 65537** against both the prior binary and an independent Python Buchberger implementation using grevlex order. All **25** cases pass: both binaries produce byte-identical full reduced bases matching Python, covering characteristic 2 and all finite-field coefficient widths. Raw artifacts live under `exact_msolve_sparse_review_runs/`, with hashes in `exact_msolve_sparse_review_results.json`.

We added the four-variable mixed chain after noticing the first 20 fixtures never actually skipped a column; at every tested characteristic, the mixed chain exercises a round importing only 2 of 6 nonpivot columns.

An initial 512-MiB test cap caused the unchanged baseline to crash with SIGSEGV before finishing its first tiny basis (saved as `initial_512mib_baseline_failure.log`). Running under the standard 2-GiB cap and 10-second per-fixture timeout succeeded across all cases, showing that failure came from the tighter limit rather than the patch.

Reproduce the independent checks:

```sh
python experiments/exact_msolve_sparse_helper_check.py
python experiments/exact_msolve_sparse_review.py
```

This review ran no full T-board model. The patch is ready for a bounded full-input trial, though small-fixture correctness does not prove the full computation will finish.
