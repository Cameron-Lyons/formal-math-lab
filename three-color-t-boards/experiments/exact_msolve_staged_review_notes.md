# Independent review of staged symbolic promotion

The sixth build passes this review. No full board solve was run here, so these checks do not produce a full ternary count or prove a memory bound for the full board.

- Reviewed executable SHA-256: `32410d78a18d426299aa6120867795b1274250d83aef69d086690630fdc981f0`
- Patch SHA-256: `53ff7198a059bcaa82a83bb0623a500b70df6074270a41c417bd4702ccdbe44e`
- Source hashes: recorded in the accompanying JSON reports and owner manifest

## Source argument

The retained-row support scan covers every column that later enters the basis. Already-present entries receive their stable basis IDs before compaction, leaving only missing entries as symbolic IDs. Before editing any mapping or exponent data, the staging helper verifies the full old symbolic-ID/column bijection, each missing mapping and flat source pointer, and the exact missing count.

Compaction walks old symbolic IDs in ascending order. Because each packed rank is at most the old ID, `memmove` always writes at or before its source slot and never overwrites an unread vector. It copies the full exponent vector (including its degree lane) while leaving retained metadata untouched. Basis insertion then walks columns in original ascending order and reads each packed rank from `hcm`, preserving the exact insertion order and basis IDs of build 5.

The slab detaches only after all selected vectors are packed. Only the symbolic table's private metadata, buckets, pointer array, and slab are freed or shrunk; borrowed `rn`, `dv`, and `dm` pointers and scalar geometry stay intact. The same `ht_t` object is restored to a valid empty secondary table before basis reservation, with every new allocation checked to exit nonzero on failure. Because `pairs_deg` is saved beforehand, later conversion reads only `hcm` and the basis table, and the usual post-conversion `clean_hash_table` remains safe.

Compaction is gated to the serial, characteristic-2, exact sparse, ordinary, non-tracing basis-export path outside normal-form and final-reduction steps, and triggers only when basis exponent capacity must actually grow (including the spare slot). Other paths keep the earlier helper, and no polynomial, coefficient, matrix row, or cubic domain changes.

## Independent executed checks

`exact_msolve_staged_review.py` extracts the support-selection, rounded-reservation, and staging code into an ASan/UBSan harness with an independent linear monomial reference (testing helper semantics rather than upstream probing):

- 1,200 valid support/mapping cases: 463 staged, 737 unchanged, 16 resets from larger tables down to 2,048 slots, and 3 zero-missing spare-boundary stages.
- Covers random and reversed old-ID/column permutations, overlapping rows, reused and missing entries, unsorted supports, full vector contents, stable IDs, rebuilt pointers, and preserved shared pointers and scalars.
- All 10 allocation-failure points and 11 malformed layouts exit nonzero with explicit errors and zero sanitizer findings (the harness's tracker cleans up on injected failure, while production exits immediately).

`exact_msolve_staged_basis_review.py` checks 12 complete F2 ideals under a 2-GiB cap against build 5 and an independent Python Buchberger solver. All 24 full-basis exports match both build 5 byte-for-byte and Python, exercising 3 staging rounds and 33 bitset rounds across coupled cubics, field extensions, a unit ideal, and a nonradical ideal (catching any accidental Boolean or radical reduction).

## Owner checks (separately attributed)

We read `exact_msolve_staged_promotion_tools/helper_check.json` and `validation.json` after completion. The owner's separate harness reports 49 upstream hash-promotion cases (with forced collisions, a direct zero-missing stage, and later insert/lookup/legacy growth/clean/copy/reinitialize/reset under sanitizers), 5 staging-allocation failures, and 18 complete-basis comparisons including non-F2 fallbacks. These belong to the owner's suite and are distinct from our independent tests above.

Reproduce the independent checks:

```sh
python experiments/exact_msolve_staged_review.py
python experiments/exact_msolve_staged_basis_review.py
```

The basis review refuses to overwrite an existing output directory; choose a fresh directory for reruns.

## Separate characteristic-three gate extension (6b)

Build 6b widens only the caller condition from characteristic 2 to characteristics 2 or 3. `exact_msolve_staged_f3_review.py` diffed all 61 C files and confirmed only that one guard in `convert.c` changed (the other 60 files, including the full staging helper, are byte-identical). The bitset kernel remains F2-only. Because staging only copies exponent vectors and remaps IDs without touching coefficients, the compaction proof and helper checks above carry over unchanged.

- Build 6b executable SHA-256: `9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a`
- One-line patch SHA-256: `96396c6b6a15e2ae1be84fdc968c21c62a87065acb5c4e2b7897b5e14cc75850`

Twelve complete F3 ideals pass against Python Buchberger and build 6: all 24 full-basis exports match byte-for-byte, exercising 3 F3 staging rounds and 0 F2 bitset rounds. Nine field-domain ideals also match exhaustive F3 point counts, while the rest test extension-field and nonradical ideals. Results and commands are in `exact_msolve_staged_f3_review_results.json`; no full board solve was run here.
