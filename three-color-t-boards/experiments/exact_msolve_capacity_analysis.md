# Independent exponent capacity is feasible

Read-only inspection of the pinned msolve source found 84 direct `esz` uses,
all in `src/neogb`. None uses exponent capacity as a bit mask. Hash probing
uses only `hsz-1`, so **bucket count must remain a power of two; exponent
capacity need not**. The exact inventory and numerical scenarios are saved
in `exact_msolve_capacity_analysis.json`.

The inspected source is commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`
with the first three local patches; `hash.c` SHA256 is
`7aa5d271c4a2923dca5a321810e0d13a1ba9e666178e5199c1719d352263db70`.
No solver was run and no source was changed for this assessment.

| Source path/function | Capacity assumption |
| --- | --- |
| `hash.c`, initializers | Initially set `esz=hsz/2`; this is an allocation policy. |
| `hash.c:319`, `enlarge_hash_table` | Doubles both explicit sizes. An arbitrary positive `esz` stays valid; power-of-two `hsz` and `hsz>=2*esz` remain invariant below the existing size limit. |
| `hash.c:132`, `copy_hash_table` | Copies `esz` and `hsz` independently and allocates/copies each array using its recorded size. |
| `hash.c:881`, `reinitialize_hash_table` | Doubles both sizes until enough capacity, reconstructs all exponent pointers, then clears metadata/buckets. No power-of-two test on `esz`. |
| `hash.c:924`, `clean_hash_table` | Clears arrays using their independent sizes; sets load to one. |
| `hash.c:1340`, `reset_hash_table` | Reallocates at the existing `esz`, clears buckets at `hsz`, and reinserts basis/pair monomials. It does not require a power-of-two exponent capacity. This ID-renumbering reset is not active in the selected ordinary F4 path. |
| `hash.c`, lookup/insertion/reinsertion | Probe with `hsz-1`; exponent IDs address `ev`/`hd` linearly. |
| `update.c:92`, `symbol.c`, `io.c`, saturation/signature/modular callers | Compare free entries or load against `esz`, then invoke the legacy grower. These comparisons are valid for arbitrary capacity. |
| `meta_data.c:340` | Prints `ceil(log2(max_esz))` as `2^k`; with arbitrary capacity this is an upper bound, not an exact capacity. Explicit capacity diagnostics should be used. |

At the observed ordered-input failure, `eld=2,078,104` and 55,218 monomials
are missing. The required next-free ID is therefore 2,133,322. Existing
exponent capacity is 2,097,152, with 4,194,304 buckets.

| Allocation policy | Exponent slots | Buckets | Principal basis arrays |
| --- | ---: | ---: | ---: |
| Before growth | 2,097,152 | 4,194,304 | 468 MiB |
| Legacy doubling | 4,194,304 | 8,388,608 | 936 MiB |
| Exact requested capacity | 2,133,322 | 8,388,608 | 491.796 MiB |
| Round request to 64K slots | 2,162,688 | 8,388,608 | 498.125 MiB |
| 12.5% growth slack | 2,359,296 | 8,388,608 | 540.5 MiB |

These calculations use the actual 202-byte exponent vectors, 16-byte metadata
records, 8-byte exponent pointers and 4-byte buckets. Rounding to 64K saves
437.875 MiB against the measured doubling at this boundary. It increases
the basis arrays by only 30.125 MiB. Matrix storage, other hash tables,
allocator overhead and possible reallocation peaks are excluded, so the
calculation does not establish that a future solver run fits or finishes.

A narrow future helper can reserve `eld+missing` rounded to 64K exponent
slots while selecting buckets independently as a power of two at least twice
that capacity. It must preserve all IDs and metadata, rebuild every `ev`
pointer after exponent-data relocation, and rebuild bucket positions when
the bucket count changes. No bucket position or data pointer may survive a
rehash; existing exponent-array IDs do survive. The existing ordinary
promotion scope is suitable, leaving the legacy grower intact elsewhere.

Necessary guards include checked load addition, checked rounding and byte
multiplication, representable 32-bit monomial IDs, a supported bucket limit
of `2^32`, and nonzero failure on every allocation error. Keeping exponent
capacity at most `2^31` retains the existing at-most-half-full policy. Small
tests should cover arbitrary capacities followed by legacy growth, copies,
clean/reset, collision-heavy lookup and stable IDs, plus completed basis
comparisons. No such new implementation is part of this analysis artifact.
