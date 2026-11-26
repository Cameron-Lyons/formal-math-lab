# Symbolic-table lifetime at basis promotion

Once linear algebra finishes, msolve can free most of the symbolic exponent table before reserving new basis-hash space. The ordinary no-trace path gives a clean ownership boundary: `convert.c` saves `pairs_deg` from the symbolic table before calling support import and only reads the basis table and column map afterwards, and `compute_new_elements` then calls `clean_hash_table(sht)` and frees the matrix containers. Trace and saturation paths must stay excluded because they may keep references across this boundary.

This analysis motivated build 6 in `exact_msolve_staged_promotion_tools` (see its README for patch and validation details; builds 1 to 5 remain untouched).

## Observed failure boundary

The non-elementary prefix trial failed right after finishing a degree-5 matrix of 210,803 rows and 6,546,994 columns. Linear algebra kept 9 output rows with 5,528,411 terms spanning 3,779,019 columns, of which 3,463,587 were missing from the basis. With basis load 1,462,002, promotion needed 4,925,590 slots (including the spare), rounding up to 4,980,736. The 3-GiB run exited nonzero with `cannot allocate promotion exponent data` after 248.070159 CPU seconds (252.145026 wall seconds), leaving no completion marker or basis.

Because secondary hash growth still doubles capacity, live symbolic load 6,546,995 puts symbolic capacity at `2^23`. For 96 variables, each exponent vector has 97 two-byte lanes, giving these principal-array sizes:

| Storage | MiB |
| --- | ---: |
| Original symbolic exponent slab | 1,552.000 |
| Symbolic metadata/pointers/buckets | 256.000 |
| Original symbolic total | 1,808.000 |
| Packed slab for missing vectors and slot zero | 640.808 |
| Required new basis principal arrays | 1,099.500 |
| Old basis exponent slab, if a moving realloc also keeps it | 291.000 |

Restoring a small empty secondary table (at most 2,048 exponent slots) adds at most 0.442 MiB, trimming roughly 1,166.75 MiB of logical symbolic storage before basis growth. The packed slab plus target basis totals about 1,740.75 MiB (or 2,031.75 MiB while a moving `realloc` holds the old basis slab). This excludes polynomial rows, matrices, libraries, and allocator bookkeeping, so it is an allocation estimate rather than a measured peak or completion guarantee. A shrinking `realloc` can still fail and must exit cleanly with no completion claim. Raw numbers and source hashes are saved in `exact_msolve_symbolic_compaction_analysis.json`.

## Implementation order

1. Complete the support scan and basis-membership lookups. Existing used columns already hold stable basis IDs, while missing columns still hold old symbolic IDs.
2. Verify the full symbolic-ID/column bijection. Scan **increasing old symbolic IDs**, pack only missing exponent vectors to the front of the same slab, and store each packed slot in `hcm`. Because the `k`-th selected old ID is at least `k`, every destination lies at or before its source and cannot overwrite an unread vector.
3. Detach the packed slab, free only the symbolic table's private metadata, buckets, and pointer array, shrink the slab, and restore the same `ht_t` object as a valid empty secondary table (never freeing or replacing borrowed `rn`, `dv`, or `dm`).
4. Reserve basis capacity, then insert vectors from the staging slab in original **ascending column order** (not packed order) so existing IDs, new insertion order, and pending pairs stay unchanged.
5. Free the staging slab. The caller can clean, grow, reset, reuse, or destroy the restored secondary table normally.

Keep the two orders separate: packing by column order risks overwriting unread vectors, while inserting by packed order can change basis IDs.

## Enabling source invariants

- `convert_hashes_to_columns` records each inverse column in `sht->hd[id].idx` before linear algebra, and ordinary LA kernels never alter `sht`.
- `convert_sparse_matrix_rows_to_basis_elements_internal` saves `pairs_deg` before import and never reads symbolic exponents afterwards.
- `compute_new_elements` clears `sht` after conversion; keeping the same `ht_t` struct keeps the pointer valid.
- `initialize_secondary_hash_table` borrows random weights and divisibility tables from the basis, and `free_hash_table` frees only private arrays (unlike `full_free_hash_table` and `free_shared_hash_data`).
- `free_meta_data` later destroys the secondary table with `free_hash_table`, so its standard ownership contract must hold.

Note that this addresses a **post-LA promotion** peak. The later elementary-e4 trial failed while growing symbolic storage *before* linear algebra; compaction after LA cannot prevent that earlier failure, and build 6 leaves the legacy symbolic grower unchanged. No unrestricted solve ran for this note.
