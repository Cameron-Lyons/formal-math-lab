# Staged symbolic promotion, sixth preserved build

This build compacts genuinely new symbolic exponent vectors in place before growing the basis table, addressing the post-linear-algebra promotion allocation failure. All five earlier builds stay untouched. Polynomial equations, coefficient arithmetic, pair selection, basis IDs, insertion order, and the legacy symbolic grower do not change.

## Provenance and scope

- Pinned upstream: msolve `v0.11.0`, commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`, archive SHA-256 `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`
- Patches: apply the five predecessor patches in `source.json`, then `staged-symbolic-promotion.patch`, SHA-256 `53ff7198a059bcaa82a83bb0623a500b70df6074270a41c417bd4702ccdbe44e`
- Frozen executable `msolve` SHA-256: `32410d78a18d426299aa6120867795b1274250d83aef69d086690630fdc981f0`
- Modified `hash.c` SHA-256: `8ff90c83d8decbec184c023cc71301a40273f9dfb2d6566e924b488b121c2f98`
- Modified `convert.c` SHA-256: `921f3fc3d01f28f622748f3dca60780fc1c962457e5b1c1639e1cce8f36e0658`

Build commands, environment (`CFLAGS=-O2 -g0`, OpenMP disabled, existing local dependencies), and library hashes are recorded in `source.json`. No system install is needed.

Destructive compaction runs only inside the support-only import path when every guard holds: F2, exact option 2, single thread, no tracer, no normal-form mode, no final-reduction step, no elimination block, basis export, and a missing count that actually forces basis exponent capacity to grow. Other modes and promotions that already fit keep the previous path. Ownership requires `st->ht == sht`, and the converter reads `pairs_deg` before consumption so all later reads touch only the basis table and `hcm`.

## Compaction proof and identity preservation

After membership lookups, each column's mask byte is `0` (unreferenced), `1` (genuinely missing), or `2` (already in the basis, with its stable basis ID stored in `hcm`). The preceding support scan covers every output row term.

Before modifying anything, the staging helper verifies the full live-ID-to-column bijection using a prefix of the retired bucket array as a bitset: all column indices must be distinct and in range, every missing entry must satisfy `hcm[column] == old_id` with a matching flat slab pointer, and the count must match the missing count. Bad mask values, inconsistent layouts, arithmetic overflow, or allocation failures exit nonzero cleanly.

Next, it scans increasing old symbolic IDs `i1 < i2 < ...`. Because the 1-based packed rank satisfies `k <= ik`, copying slot `ik` to slot `k` with `memmove` never overwrites an unread source vector (slot 0 stays reserved). Each packed entry updates `hcm[column]` to its rank, and the final packed count is rechecked.

The detached slab holds `missing + 1` exponent vectors. Private symbolic metadata, buckets, and exponent pointers are freed, and a checked shrinking `realloc` drops the unused slab tail (exiting nonzero on failure before any completion marker can print).

Basis import still walks missing columns in original ascending column order, reading each vector from its packed slot in `hcm` and calling the unchanged insertion routine. Existing basis IDs stay untouched, new IDs match build 5's order, and the postcondition confirms `inserted == missing`. Coefficients, row supports, and pending pairs stay unchanged.

## Ownership and secondary-table reuse

Before basis reservation starts, the same secondary `ht_t` object is restored to a valid empty table: exponent capacity `min(old_capacity, 2048)`, twice as many buckets (both powers of two), load 1, and valid pointers for every slot. Scalar order/layout fields and borrowed `rn`, `dv`, and `dm` pointers stay intact; only private arrays are replaced, and neither `full_free_hash_table` nor `free_shared_hash_data` is called.

The detached staging slab is freed once all missing monomials are inserted. Both `sht` and `md->ht` continue pointing to the valid restored empty table, so `clean_hash_table`, later insertions, legacy growth, copy, reset/reinsert, and `free_meta_data` all work normally. The pre-LA stats still record historical peak symbolic capacity. Shrinking the secondary table can add regrowth work in later rounds, while giving the next F4 round the exact empty table it expects.

After compaction and empty-table restoration succeed, verbosity 2 prints:

```
MSOLVE_SYMBOLIC_STAGING old_load=L old_capacity=C missing=M old_exponent_bytes=B staged_exponent_bytes=S reset_capacity=R
```

These numbers log logical allocation sizes rather than measured RSS or a completed basis.

## Memory estimate and limits

At the observed non-e4 failure boundary, a secondary table of capacity `2^23` with 97 two-byte lanes takes 1,808 MiB across its four principal arrays. Packing 3,463,587 missing vectors takes 640.808 MiB plus at most 0.442 MiB for the restored small table, dropping logical symbolic memory by roughly 1,166.75 MiB before basis growth. The new basis principal arrays take 1,099.5 MiB (plus up to 291 MiB temporarily if a moving `realloc` holds the old basis slab). Polynomial rows and other allocations are excluded, so this estimate does not guarantee a full solve fits or finishes.

The separate e4 trial failed while growing symbolic storage *before* linear algebra. This patch cannot fix that earlier failure or shrink the final persistent basis, and leaves the legacy grower unchanged outside this path.

## Completed validation

- **`helper_check.py`**: extracts actual upstream lookup, insertion, reserve, staging, clean, copy, secondary init, reinit, reset, and legacy growth under ASan/UBSan (stubbing only divisibility masks and timers). Passes 49 promotion/reuse cases (including 23 reversed column permutations in normal and forced-collision modes, reused/unreferenced columns, all-known no-growth, direct zero-missing stage, and large-capacity reset to 2,048), matching noncompacting IDs and vectors plus later clean/grow/copy/reset ops. All 5 new allocation sites (slab shrink plus 4 fresh private arrays) fail cleanly when fault-injected (leak detection enabled on normal runs, disabled on intentional fatal exits).
- **`validation.json`**: 18 completed `-g 1` / `-g 2` comparisons byte-identical to build 5, including the six-completion F2 prefix (dim 12, 6 boards across both bigint counters) and an F29 regression; 2 small runs trigger staging.
- **`mode_validation.json`**: 4 fallback comparisons (LA option 1, 2 threads, elimination order, characteristic 5), all byte-identical to build 5 with no staging.
- **Independent review (`../exact_msolve_staged_review_results.json`, `../exact_msolve_staged_basis_review_results.json`)**: ASan/UBSan checks on 1,200 extracted-helper cases (463 staged, 737 unchanged, 16 resets to 2,048, 3 zero-missing boundary stages, 10 allocation failures, 11 invalid layouts) using an independent linear reference, plus 12 complete F2 ideals (24 exports byte-identical to build 5 and matching Python Buchberger, exercising 3 staging rounds and 33 bitset rounds).
- **`f3_validation.json`**: compatibility check on the audited natural F3 19-variable, 99-generator fixed fiber (byte-identical to build 5; dimension 6 directly across both bigint counters, no divisor; staging gate stays F2-only in this build).

No full T-board count was run during validation.
