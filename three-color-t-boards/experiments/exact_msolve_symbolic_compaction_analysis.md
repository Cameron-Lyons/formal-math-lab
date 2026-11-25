# Symbolic-table lifetime at basis promotion

The completed matrix can release its full symbolic exponent table before
reserving the next basis block. The ordinary no-trace path has a suitable
ownership boundary: `convert.c` saves `pairs_deg` from the symbolic table
before calling support import, and afterwards reads only the basis table
and column-to-basis map. `compute_new_elements` next calls
`clean_hash_table(sht)` and discards the matrix containers. No trace or
saturation reference may be retained across this destructive boundary.

This analysis motivated the separately preserved sixth build in
`exact_msolve_staged_promotion_tools`. The first five builds remain unchanged.
Its patch and validation are documented in that directory's README.

The observed non-elementary prefix trial failed after a completed degree-five
matrix of 210,803 rows and 6,546,994 columns. It retained nine output rows
with 5,528,411 terms. Their support referenced 3,779,019 columns, of which
3,463,587 were absent from the basis. Basis load 1,462,002 therefore required
4,925,590 slots including the spare; rounded reservation requested 4,980,736.
The exact terminal diagnostic was `cannot allocate promotion exponent data`.
The 3 GiB trial exited nonzero after 248.070159 CPU seconds / 252.145026 wall
seconds, without an export marker or completed basis.

Secondary hash growth still doubles capacity. Given the live symbolic load
6,546,995 and the preceding smaller rounds, its capacity at this boundary is
2^23. For 96 variables each exponent vector has 97 entries of two bytes.
The resulting principal-array estimate is:

| Storage | MiB |
| --- | ---: |
| Original symbolic exponent slab | 1,552.000 |
| Symbolic metadata/pointers/buckets | 256.000 |
| Original symbolic total | 1,808.000 |
| Packed slab for missing vectors and slot zero | 640.808 |
| Required new basis principal arrays | 1,099.500 |
| Old basis exponent slab, if a moving realloc also retains it | 291.000 |

The implementation restores a small empty secondary table, at most 2,048
exponent slots, adding at most 0.442 MiB. Thus it removes approximately
1,166.75 MiB of logical symbolic allocation before basis growth at the
observed boundary. The packed slab plus the target basis is about
1,740.75 MiB; including the old basis exponent slab during a moving realloc
gives about 2,031.75 MiB. This excludes polynomial rows, matrices, libraries,
allocator bookkeeping and other state. It is an allocation model, not a
measured large-run peak or a guarantee of completion. A checked shrinking
realloc can still fail; that must end the run without a completion claim.

The raw arithmetic and pinned source hashes are in
`exact_msolve_symbolic_compaction_analysis.json`.

The key implementation order is:

1. Finish the existing support scan and basis-membership lookups. Used
   existing columns already hold their stable basis IDs; genuinely missing
   columns still hold old symbolic IDs.
2. Verify the complete symbolic-ID/column bijection. Iterate **old symbolic
   IDs increasingly**, pack only missing exponent vectors into the beginning
   of the same contiguous slab, and update their `hcm` entries to packed
   positions. The kth selected old ID is at least k, so each destination is
   at or before its source and cannot overwrite an unread future vector.
3. Detach the packed slab; free only the symbolic table's private metadata,
   bucket and pointer arrays; shrink the slab; restore the same `ht_t` object
   as a valid empty secondary table. Never free or replace the borrowed
   `rn`, `dv` or `dm` data.
4. Reserve basis capacity, then insert from the staging slab in the original
   **ascending column order**, not in packed order. Existing basis IDs,
   relative new insertion order and pending-pair references are unchanged.
5. Free the staging slab. The caller can immediately clean, grow, reset,
   reuse or destroy the restored secondary table normally.

The old-ID packing order and the column insertion order solve different
problems and must not be conflated. Packing by column order can overwrite an
unread source exponent; inserting by packed order can change basis IDs.

The following source facts make this boundary usable:

- `convert_hashes_to_columns` stores each inverse column in `sht->hd[id].idx`
  before linear algebra; the ordinary LA kernels do not modify that table.
- `convert_sparse_matrix_rows_to_basis_elements_internal` captures
  `pairs_deg` before import and does not subsequently dereference symbolic
  exponent data.
- `compute_new_elements` clears the symbolic table after conversion. Its
  pointer remains valid because the object itself is not replaced.
- `initialize_secondary_hash_table` borrows random weights and divisibility
  data from the basis. `free_hash_table` frees only private arrays;
  `full_free_hash_table`/`free_shared_hash_data` would be wrong here.
- `free_meta_data` later destroys the restored secondary table via
  `free_hash_table`, so its ordinary ownership contract must remain intact.

This change addresses a **post-LA promotion** peak. The later elementary-e4
trial failed while enlarging symbolic exponent storage before linear algebra.
That earlier failure cannot be prevented by this compaction boundary, and
the sixth build does not change the legacy symbolic grower. No unrestricted
solver run was launched by this analysis or build-validation task.
