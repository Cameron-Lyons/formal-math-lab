# Independent review of staged symbolic promotion

The sixth build passes this review. No full board computation was run by this reviewer, and these checks do not establish a full ternary count or a memory bound for a full computation.

Reviewed executable SHA256: `32410d78a18d426299aa6120867795b1274250d83aef69d086690630fdc981f0`.
Patch SHA256: `53ff7198a059bcaa82a83bb0623a500b70df6074270a41c417bd4702ccdbe44e`.
The source hashes are recorded in the accompanying results and owner manifest.

## Source argument

The retained-row support scan covers every column that will subsequently be converted into a basis entry. Existing entries become stable basis IDs before compaction; only missing entries remain symbolic IDs. The staging helper checks the complete old symbolic-ID/column bijection, checks each missing mapping and flat source pointer, and checks the missing count before modifying mappings or exponents.

Compaction scans old symbolic IDs in ascending order. The packed rank is at most the old ID, so each `memmove` writes entirely at or before the current source slot and cannot overwrite an unread later source. It copies the whole exponent vector, including degree metadata stored in the vector. The retained metadata array is not overwritten during this pass. Subsequent insertion scans columns in their original ascending order and reads the compact rank from `hcm`; it therefore preserves the previous insertion order and resulting basis IDs.

The slab is detached only after all selected vectors have been packed. Only the symbolic table's private metadata, buckets, pointer array and slab are freed or resized. Shared `rn`, `dv`, and `dm` pointers and scalar geometry are preserved. The same table object is restored to an empty, valid secondary table before the basis reserve. All new allocations are checked and fail with a nonzero exit. `pairs_deg` is captured before staging; after promotion, conversion reads retained terms through `hcm` and basis metadata, with no need for the retired symbolic entries. The subsequent ordinary symbolic-table clean remains valid.

The caller permits consumption only in the guarded serial, characteristic-two, exact sparse, ordinary, non-tracing basis-export path, outside normal-form and final-reduction operations. Staging additionally requires actual basis-capacity growth, including the spare-slot condition. Other paths retain the previous helper behavior. No polynomial, coefficient, matrix row, or ordinary cubic-domain equation is changed by this patch.

## Independent executed checks

`exact_msolve_staged_review.py` extracts the actual support-selection, rounded-reservation and staging functions into a separate C harness. It uses an independent linear monomial lookup and insertion reference; it does not claim to test upstream probing. Under AddressSanitizer and UndefinedBehaviorSanitizer it passed:

- 1,200 valid mapping/support cases: 463 staged, 737 unchanged, 16 resets from a larger table to 2,048 slots, and three zero-missing spare-boundary stages.
- Random and reversed old-ID/column permutations, overlapping output rows, reused and missing entries, unsorted retained supports, complete vector contents, stable insertion IDs, pointer reconstruction, shared-pointer preservation and scalar preservation.
- All ten allocation-failure points on the complete helper path and eleven malformed layouts. Every failure returned nonzero with an explicit error, and none produced sanitizer findings. The harness's allocation tracker cleans allocations on deliberate failure; the production process exits immediately.

`exact_msolve_staged_basis_review.py` passed twelve complete characteristic-two ideals against the prior fifth executable and an independent Python Buchberger implementation. All 24 full basis exports were byte-identical across executables and equal to the independent reduced bases. The candidate exercised three actual staging rounds and 33 bitset rounds. Cases include coupled cubic domains, field extensions, a unit ideal and a nonradical ideal, so an accidental Boolean or radical reduction would fail these comparisons. These small solver executions used a 2 GiB address-space limit and no full board input.

## Separately attributed owner checks

The owner artifacts `exact_msolve_staged_promotion_tools/helper_check.json` and `validation.json` were read after completion. The owner reports 49 actual upstream hash-promotion cases, forced collisions, a direct zero-missing stage, and subsequent insert/lookup/legacy growth/clean/copy/reinitialize/reset operations under sanitizers. Its five staging-allocation failures fail explicitly. Its eighteen integrated complete-basis comparisons also pass, including non-characteristic-two fallback. Those are the owner's tests, distinct from the independently executed checks above.

Reproduce the independent checks with:

```sh
python experiments/exact_msolve_staged_review.py
python experiments/exact_msolve_staged_basis_review.py
```

The basis review deliberately refuses an existing output directory; preserve prior artifacts and choose a fresh directory before repeating it.

## Separate characteristic-three gate extension

The preserved 6b build extends only the caller condition from characteristic two to characteristics two or three. `exact_msolve_staged_f3_review.py` compared all C sources: only that condition in `convert.c` changes; the other 60 C files, including the complete staging helper, are byte-identical. The F2-only bitset kernel remains restricted to characteristic two. The compaction proof and independent helper failure checks above apply without change because staging only copies exponent vectors and remaps identifiers; it does not inspect or modify coefficients.

The 6b executable SHA256 is `9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a`, and its one-line patch SHA256 is `96396c6b6a15e2ae1be84fdc968c21c62a87065acb5c4e2b7897b5e14cc75850`.

Twelve complete characteristic-three ideals independently pass against Python Buchberger and the frozen sixth executable: 24 full basis exports match byte-for-byte, with three actual F3 staging rounds. Nine field-domain fixtures also match exhaustive F3 assignment counts. The other fixtures include an extension-field ideal and a nonradical ideal, preserving ordinary polynomial semantics beyond field-domain cases. No F2 bitset round appears in any F3 run. Results and commands are retained in `exact_msolve_staged_f3_review_results.json`; no full board solve was run by this reviewer.
