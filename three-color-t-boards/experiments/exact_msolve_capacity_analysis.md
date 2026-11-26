# Independent exponent capacity is feasible

A read-only audit of the pinned msolve source found 84 direct uses of `esz`, all inside `src/neogb`. None uses exponent capacity as a bit mask. Hash probing masks only with `hsz-1`, so **the bucket count must stay a power of two, while the exponent capacity does not have to**. The full inventory and numerical scenarios are saved in `exact_msolve_capacity_analysis.json`.

This audit inspected commit `cc044551f8e202d00691990fd3fd0b1226a88ea2` with the first three local patches applied (`hash.c` SHA-256 `7aa5d271c4a2923dca5a321810e0d13a1ba9e666178e5199c1719d352263db70`). No solver was run and no source file was edited.

| Source path/function | Capacity assumption |
| --- | --- |
| `hash.c`, initializers | Initially sets `esz = hsz / 2` as an allocation policy. |
| `hash.c:319`, `enlarge_hash_table` | Doubles both sizes. Any positive `esz` stays valid; power-of-two `hsz` and `hsz >= 2*esz` hold below the existing size limit. |
| `hash.c:132`, `copy_hash_table` | Copies `esz` and `hsz` separately and allocates/copies each array by its own recorded size. |
| `hash.c:881`, `reinitialize_hash_table` | Doubles both sizes until capacity is enough, rebuilds all exponent pointers, and clears metadata and buckets. No power-of-two test on `esz`. |
| `hash.c:924`, `clean_hash_table` | Clears arrays using their independent sizes and sets load to 1. |
| `hash.c:1340`, `reset_hash_table` | Reallocates at the current `esz`, clears buckets at `hsz`, and reinserts basis and pair monomials. Does not require power-of-two `esz`. This ID-renumbering reset is inactive in the selected ordinary F4 path. |
| `hash.c`, lookup/insertion/reinsertion | Probes with `hsz - 1`; exponent IDs index `ev` and `hd` linearly. |
| `update.c:92`, `symbol.c`, `io.c`, saturation/signature/modular callers | Compare free entries or load against `esz`, then call the legacy grower. Valid for any capacity. |
| `meta_data.c:340` | Prints `ceil(log2(max_esz))` as `2^k`; for arbitrary capacities this becomes an upper bound rather than an exact value, so explicit capacity diagnostics are needed. |

At the observed ordered-input failure, `eld = 2,078,104` and 55,218 monomials were missing, so the required next-free ID was 2,133,322. Current exponent capacity was 2,097,152 with 4,194,304 buckets.

| Allocation policy | Exponent slots | Buckets | Principal basis arrays |
| --- | ---: | ---: | ---: |
| Before growth | 2,097,152 | 4,194,304 | 468 MiB |
| Legacy doubling | 4,194,304 | 8,388,608 | 936 MiB |
| Exact requested capacity | 2,133,322 | 8,388,608 | 491.796 MiB |
| Round request to 64K slots | 2,162,688 | 8,388,608 | 498.125 MiB |
| 12.5% growth slack | 2,359,296 | 8,388,608 | 540.5 MiB |

These figures count the actual 202-byte exponent vectors, 16-byte metadata records, 8-byte exponent pointers, and 4-byte buckets. Rounding to 64K saves 437.875 MiB compared to doubling at this boundary, adding only 30.125 MiB to the basis arrays. Matrix storage, other hash tables, allocator overhead, and reallocation peaks are left out, so these numbers do not prove a future run will fit or finish.

A focused helper for the ordinary promotion path can reserve `eld + missing` rounded up to 64K exponent slots while choosing the bucket count separately as a power of two at least twice that capacity, leaving the legacy grower unchanged elsewhere. It must:

- Keep all existing monomial IDs and metadata intact.
- Rebuild every `ev` pointer after exponent-data relocation.
- Rebuild bucket positions whenever the bucket count changes (no bucket position or data pointer may survive a rehash, while exponent-array IDs do survive).
- Guard load addition, rounding, and byte multiplication against overflow, keep monomial IDs within 32 bits, keep buckets at most `2^32` and exponent capacity at most `2^31` (preserving the at-most-half-full rule), and exit nonzero on any allocation failure.

Before deploying such a helper, small tests should exercise arbitrary capacities followed by legacy growth, copies, clean/reset, collision-heavy lookup, stable IDs, and completed basis comparisons. No code changes are part of this analysis.
