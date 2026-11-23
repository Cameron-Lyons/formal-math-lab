# Independent retained-column promotion review

The reviewed patch is
`exact_msolve_sparse_promotion_tools/retained-column-promotion.patch`, SHA256
`3955ca519da0b32a5e000792d7d36000d45a8971eea8fb56d1e793cd40a0edeb`.
The candidate executable SHA256 is
`997199fc836584627dc1c6324fc2702a4d900f4cee84d4534acd89f29a068093`.
The previous export-only executable remains unchanged at
`2d3258dd099a34410b05eadd21dbb38db22b8be0962ab59115d01660652c355d`.

## Source and semantic review

The original `switch_hcm_data_to_basis_hash_table` reserves and imports every
column in the nonpivot block `[ncl,nc)`. Its only direct caller is the sparse
matrix-to-basis conversion helper. The proposed optimization imports the union
of supports of retained output rows, using a byte mask of length `ncr`.

The new helper scans every entry in every retained row:
`mat->tr[i][OFFSET+j]` for `i<mat->np` and `j<row[LENGTH]`. It does not confuse
retained pivots with full row supports. It validates dimensions, nonempty row
pointers and lengths, each referenced column's range, and each symbolic hash.
It deduplicates references, reserves enough space for their union, and inserts
them in ascending column order. Referenced entries of `hcm` are replaced by
basis hash IDs; unused entries remain unchanged.

This preserves the mathematical polynomials because the following conversion
maps only terms actually appearing in retained rows. Coefficient arrays,
their indices, row term order, and basis-row ordering are unchanged. Existing
basis IDs are preserved; new retained IDs can differ from the old program
because unused monomials are no longer inserted. Those numeric differences
are harmless in the ordinary path, where IDs refer consistently to exponent
vectors and pending pairs retain their existing IDs.

Numeric ID differences are **not** safe to assume harmless for trace replay.
Learning/application modes compare leading-monomial hash IDs directly, and
supports can differ across primes. This issue was reported before the patch
was finalized. The actual optimized call is restricted to
`compute_new_elements` with all these conditions:

```text
trace_level == NO_TRACER
laopt == 2
fc > 0
nev == 0
print_gb > 0
```

The old-signature conversion wrapper still selects the original all-column
helper. All other callers, including trace, modular, saturation, and final
reduction paths, retain that wrapper. Thus the patch does not alter their
hash-insertion assumptions. On the ordinary path, the symbolic table and
matrix are cleared after conversion, and the next column construction
repopulates the mapping; unused symbolic entries are not subsequently read
as retained basis terms.

Mask allocation and explicit invariant violations terminate nonzero with an
error. The upstream `enlarge_hash_table` still contains unsafe `realloc`
handling; this patch does not repair that allocator. Allocation failure may
therefore still terminate with a segmentation fault. The backend treats such
termination as failure and emits no completed count. This is a limit of
robustness and memory availability, not permission to interpret failure as
an empty solution set.

## Independent executable checks

`exact_msolve_sparse_helper_check.py` extracts the exact new helper from the
candidate source and compiles it against an instrumented minimal hash table
using address and undefined-behavior sanitizers. It passed:

- 5,000 deterministic randomized cases with shared supports, reused existing
  basis entries, shuffled column mappings, and varying retained row lengths.
- Checks that every referenced monomial maps correctly, all previous IDs and
  row metadata remain intact, unused columns remain unchanged, and new
  retained insertions occur in ascending column order.
- Twelve rejection cases covering invalid dimensions, row pointers/lengths,
  out-of-block columns, invalid symbolic hashes, and mask allocation failure.

The harness stubs the hash allocator. It does not claim to verify the
upstream allocator's memory-failure behavior.

`exact_msolve_sparse_review.py` independently implements exact Buchberger
reduction in Python over a prime field with grevlex order. It compared full
reduced bases for five small systems at each of **2, 5, 29, 257, and 65537**:
root sums, root products, a mixed cubic system, a quadratic cycle, and a
four-variable mixed chain.
All **25** cases passed: the previous and candidate binaries' exported bases
are byte-identical and both match the independent Python basis. These cover
characteristic two and the backend's different finite-field coefficient
widths. Raw inputs, logs, and basis exports are retained under
`exact_msolve_sparse_review_runs/`; result hashes are in
`exact_msolve_sparse_review_results.json`.

The mixed-chain fixture was added after noticing that the initial twenty
fixtures exercised mapping but did not actually omit any unused columns.
At every tested characteristic, the mixed chain exercises a round importing
only two of six nonpivot columns. Thus the independent full-basis comparison
also checks a real change in the promoted monomial set.

An initial harness limit of 512 MiB caused the unchanged baseline to terminate
with SIGSEGV before calculating its first tiny basis. The original failure
log is retained as `initial_512mib_baseline_failure.log`. All comparisons were
then run under the intended 2 GiB address-space limit, with a ten-second
per-fixture timeout, and completed successfully. This was not a discrepancy
between the baseline and selective-import implementations.

Reproduce the independent checks with:

```sh
python experiments/exact_msolve_sparse_helper_check.py
python experiments/exact_msolve_sparse_review.py
```

No full T-board model was run by this review. The patch is ready for a bounded
full-input comparison; the tests establish its correctness on the audited
path and small fixtures, not that the unrestricted computation will finish.
