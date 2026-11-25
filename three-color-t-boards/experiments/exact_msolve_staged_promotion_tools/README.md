# Staged symbolic promotion, sixth preserved build

This build compacts genuinely new symbolic exponent vectors in place before
growing the basis table. It targets the measured post-linear-algebra promotion
allocation failure. All five predecessor builds are preserved. It does not
change polynomial equations, coefficient arithmetic, pair selection, basis
IDs or insertion order, and does not modify the legacy symbolic grower.

## Provenance and scope

Pinned upstream is msolve v0.11.0, commit
`cc044551f8e202d00691990fd3fd0b1226a88ea2`; archive SHA256
`0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`.
Apply the five predecessor patches recorded in `source.json`, then
`staged-symbolic-promotion.patch`, SHA256
`53ff7198a059bcaa82a83bb0623a500b70df6074270a41c417bd4702ccdbe44e`.

Frozen executable: `msolve`, SHA256
`32410d78a18d426299aa6120867795b1274250d83aef69d086690630fdc981f0`.
Modified `hash.c`: SHA256
`8ff90c83d8decbec184c023cc71301a40273f9dfb2d6566e924b488b121c2f98`.
Modified `convert.c`: SHA256
`921f3fc3d01f28f622748f3dca60780fc1c962457e5b1c1639e1cce8f36e0658`.

Build commands and local dependency/library hashes are in `source.json`.
The same existing local dependencies and `CFLAGS=-O2 -g0` are used, with
OpenMP disabled. No system installation is required.

Destructive compaction is enabled only in the existing support-only import
path, further restricted to F2, exact option two, one thread, no tracer, no
normal-form computation, no final-reduction step, no elimination block and
basis export. It is triggered only when the exact missing count requires
additional basis exponent capacity. Other fields/modes and promotions that
fit their current basis allocation retain the previous behavior.

The mutable ownership token must be exactly `st->ht == sht`. The surrounding
converter captures `pairs_deg` before this table may be consumed; all later
conversion reads use the basis table and `hcm`.

## Compaction proof and identity preservation

After existing membership lookups, mask value zero denotes an unreferenced
column, one a genuinely missing monomial and two an already present basis
monomial. The last group already has its stable basis ID in `hcm`. Every
output row term was included by the preceding support scan.

The staging helper verifies the entire live-ID-to-column bijection using a
small prefix of the now-retired private bucket array as a bitset. All column
indices must be distinct and in range. For every missing entry,
`hcm[column] == old_id` and its exponent pointer must match the contiguous
slab layout. The count must equal the previously computed missing count.
Mask values outside zero/one/two, inconsistent layouts, arithmetic overflow
and allocation failure terminate nonzero.

It then scans **increasing old symbolic IDs**. If the selected IDs are
`i1 < i2 < ...`, their one-based ranks satisfy `k <= ik`. Copying the vector
at `ik` to slot `k` therefore cannot overwrite a source whose old ID has not
yet been visited. `memmove` handles same-block overlap, and slot zero is
reserved. `hcm[column]` is updated to the packed rank. The final packed count
is checked again.

The detached slab contains `missing+1` exponent vectors. Private symbolic
metadata, bucket storage and exponent-pointer arrays are freed; a checked
shrinking realloc releases the unused slab suffix. A failed shrink retains
no success status and exits before the eventual basis-export marker.

Basis import still visits missing columns in the original **ascending
column order**. It reads each vector from the packed slot recorded in `hcm`
and calls the unchanged insertion function. Existing IDs do not change;
new IDs are assigned in precisely the same order as the fifth build. The
existing postcondition verifies that the number of actually inserted
monomials equals the exact missing count. Coefficients, row supports and
pending-pair semantics are unchanged.

## Ownership and secondary-table reuse

The same secondary `ht_t` object is restored before basis reservation. Its
fresh exponent capacity is `min(old_capacity, 2048)`, with twice as many
buckets, load one and valid pointers for every slot. Both capacities are
powers of two. Its scalar order/layout fields and borrowed `rn`, `dv`, `dm`
pointers remain unchanged. Only private arrays are replaced; neither
`full_free_hash_table` nor `free_shared_hash_data` is called.

The staging slab temporarily has separate local ownership, and is freed
after all missing monomials have been inserted. The caller's existing local
`sht` pointer and `md->ht` still refer to the same valid empty object. The
usual `clean_hash_table` call is therefore safe, as are subsequent insertion,
legacy growth, copy, reset/reinsert and final `free_meta_data` cleanup.

The historical maximum symbolic capacity remains recorded by the existing
pre-LA statistic update. Resetting its current storage capacity is deliberate
and can add future regrowth work. It does not change the logical empty table
that the next F4 round expects.

The diagnostic is printed only after successful compaction and empty-table
restoration:

```
MSOLVE_SYMBOLIC_STAGING old_load=L old_capacity=C missing=M old_exponent_bytes=B staged_exponent_bytes=S reset_capacity=R
```

It reports logical allocation sizes, not measured RSS or a completed basis.

## Memory estimate and limits

At the observed non-e4 boundary, a secondary capacity of 2^23 with 97
two-byte exponent entries occupies 1,808 MiB in its four principal arrays.
The 3,463,587 missing vectors need a 640.808 MiB staging slab, plus at most
0.442 MiB for the restored small table. That is a projected reduction of
about 1,166.75 MiB before basis growth. The new basis's principal allocations
are 1,099.5 MiB; a moving realloc may additionally retain its old 291 MiB
exponent slab temporarily. Polynomial storage and other allocations are not
included. This is not a measured large-run saving or a completion guarantee.

The separate e4 run failed while constructing its next symbolic matrix,
before this boundary. This patch cannot fix that earlier failure. It also
cannot reduce the size of the eventual persistent basis. The original
legacy grower's allocation behavior remains unchanged outside this scope.

## Completed owner validation

- `helper_check.py` extracts the actual upstream lookup, insertion, reserve,
  staging, clean, copy, secondary initialization, reinitialization, reset
  and legacy growth functions. ASan/UBSan pass 49 promotion/reuse cases,
  including 23 reversed column permutations in each of normal and forced
  collision modes. Selected/reused/unreferenced columns, an all-known
  no-growth path, a direct zero-missing stage, and large-capacity reset to
  2048 slots are included. Basis IDs and exponent vectors match the
  noncompacting path. Subsequent clean/grow/copy/reset operations pass.
- All five new allocation sites are fault-injected: one slab shrink and
  four fresh private allocations. Each exits nonzero with the expected
  diagnostic, without sanitizer findings or a completion marker. Normal
  tests enable leak detection; intentional fatal-exit tests disable leak
  reporting. Divisibility-mask generation and timers are the only stubs.
- `validation.json` records 18 complete leading/full-basis comparisons,
  byte-identical to the fifth build, including the known six-completion F2
  prefix and an F29 regression. Both bigint counters preserve quotient 12
  and prefix count six. Two completed small-basis runs exercise actual
  symbolic staging, with recorded diagnostics.
- `mode_validation.json` adds four completed fallback comparisons for
  exact sparse-dense option one, requested thread count two, elimination
  order and characteristic five. Outputs are byte-identical to the fifth
  build and do not enter symbolic staging.

Independent review also passed against these frozen hashes:

- `../exact_msolve_staged_review_results.json` checks the actual extracted
  helpers under ASan/UBSan on 1,200 cases: 463 staged, 737 unchanged,
  16 large-to-2048 resets and three zero-missing boundary stages. Independent
  linear lookup verifies vectors, mappings, stable IDs and all borrowed
  pointers/scalars. Ten allocation failures and eleven invalid layouts
  terminate nonzero. This is separate from the owner's actual upstream
  lookup/growth/reset harness.
- `../exact_msolve_staged_basis_review_results.json` verifies twelve complete
  F2 ideals, with 24 exports byte-identical to the fifth build and equal to
  a Python Buchberger reference. Three actual staging rounds and 33 bitset
  rounds are exercised.

`f3_validation.json` additionally checks the parent-audited natural F3
nineteen-variable, 99-generator fixed fiber. Both leading/full exports are
byte-identical to the fifth build; both bigint counters give dimension six
directly, with no extension divisor. The frozen staging gate is F2-only, so
this is a compatibility check and does not enable compaction for F3.

No full T-board count was run by this build-validation task.
