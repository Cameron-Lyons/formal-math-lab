# Rounded exponent storage for basis promotion

This fourth preserved build grows basis exponent storage to the required
number of entries rounded to 64K slots. Hash buckets remain a separate
power-of-two allocation. It is limited to the previously reviewed ordinary,
exact, non-tracing F4 promotion path. The original grower and all three
preceding builds remain unchanged.

The measured failure motivating this change had basis load 2,078,104 with
55,218 genuinely missing monomials. The old grower doubled capacity from
2,097,152 to 4,194,304 slots. The new reservation would request 2,162,688
slots and 8,388,608 buckets. For the 100-variable layout that is 498.125 MiB
in principal basis arrays, compared with 936 MiB after doubling: a saving of
437.875 MiB at that boundary. This arithmetic excludes matrix storage,
other hash tables and reallocation peaks; it does not establish an exact
T-board count or guarantee completion under 2 GiB.

## Pinned provenance

- Upstream: <https://github.com/algebraic-solving/msolve>, `v0.11.0`, commit
  `cc044551f8e202d00691990fd3fd0b1226a88ea2`.
- Original archive SHA256:
  `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`.
- Apply the three predecessor patches in `source.json`, then the incremental
  `rounded-promotion-capacity.patch`, SHA256
  `d569538b42f58dbf7160621891918cddc9496347a8229f350350eb5977539461`.
- Executable: `msolve`, SHA256
  `cebd842aa617f09725a1f5429ebc822da238563f142b14993cccb85312d1874c`.
- Preserved missing-only baseline SHA256:
  `1e2111b5e1ef28201f3b2da6bc727d4563569e96b3468ab241433e7d2238a202`.
- Final `src/neogb/hash.c` SHA256:
  `81104b9e535ff3cc057611238a9987c718099f0ba2431d38c734d667e662aefd`.

The source manifest records archive/patch/file/library hashes and the exact
build environment. Commands were `./autogen.sh`,
`./configure --disable-shared --enable-static --disable-openmp`, and
`make -j1`; their wall times were 5.86, 12.45 and 26.05 seconds. The recorded
environment uses `CFLAGS=-O2 -g0` and the existing local dependencies under
`../exact_algebra_backend_root/usr`. No system installation was used.

## Reservation and compatibility

`reserve_basis_hash_table_for_promotion` receives the exact missing count
from the third build. It reserves `eld + missing + 1`, rounded upward to a
multiple of 65,536. The spare entry handles legacy sites that grow on
`eld == esz-1`: an exact-fit promotion cannot leave `eld == esz`.

The helper checks load addition, rounding limits and every allocation byte
product. Supported exponent capacity is at most `2^30`, with buckets at most
`2^31`. This conservative limit avoids an existing legacy reset routine that
narrows `hsz` to a 32-bit integer at `2^32`. Buckets must be a nonzero power
of two and at least twice exponent capacity. Bucket capacity grows only when
needed to maintain that inequality.

Metadata, exponent-pointer and exponent-data reallocations use checked
temporary pointers. Every `ev` pointer, including slot zero, is reconstructed
after data relocation. If buckets grow, the map is cleared and all existing
entry IDs are reinserted using their preserved hash values. The IDs,
exponents, coefficients, pending-pair references and insertion order remain
unchanged. Every allocation or unsupported-state failure exits nonzero
before any later basis-completion marker. The legacy allocator is unchanged
for all other callers and retains its own upstream failure behavior.

`esz` is an ordinary array bound throughout copy/reset/clean and legacy
growth; only `hsz` is used in bit-mask probing. Source inventory and memory
calculations are in `../exact_msolve_capacity_analysis.md` and `.json`.
The old final statistics print `ceil(log2(max_esz))`, so their `2^k` notation
becomes a rounded upper bound. Use the explicit new diagnostic instead:

```
MSOLVE_PROMOTION_CAPACITY_REQUEST required_with_spare=R exponent_old=A exponent_new=B buckets_old=C buckets_new=D
```

This diagnostic reports a request before allocation, not successful
completion. The existing post-import diagnostic and final export marker
retain their established meanings.

## Completed validation

- All 16 owner comparisons passed: seven small ideals and the known
  six-completion ternary prefix, both `-g1` and `-g2`, byte-identical to the
  third build. Both bigint counters retain quotient dimension 12 and board
  count 6 for that prefix. `-s4` forces a tiny initial hash; two logged
  promotions actually use the new grower. Commands, artifacts, limits and
  hashes are recorded in `validation.json`.
- Independent review passed 25 complete small bases across five prime
  characteristics, including characteristic two. They match the third build
  and an independent Python Buchberger reference. Ten rounded-growth events
  were observed. See `../exact_msolve_rounded_review_results.json`.
- The independent exact-helper ASan/UBSan checks passed three real
  reallocation/collision cases, four injected reallocation failures, seven
  independently calculated plans and 13 invalid-layout/overflow cases.
  They include non-power-of-two capacity 196,608 and the unchanged-bucket
  branch. See `../exact_msolve_rounded_capacity_results.json`.
- `compatibility_check.py` uses the actual upstream lookup, insertion,
  copy, clean, reinitialize, secondary-initialization, reset/reinsert and
  legacy enlargement functions. In normal and deliberately colliding hash
  modes, capacity 196,608 grows through the old grower to 393,216; every
  existing ID/exponent survives. Copies and secondary tables remain usable.
  Legacy reset intentionally renumbers IDs; every referenced monomial is
  checked afterwards. An exact-boundary spare-slot case also passes.
  ASan/UBSan report no findings. Exact source hashes and output are in
  `compatibility_check.json`.

The compatibility harness stubs only divisibility-mask generation and timing
functions. Allocation failures are covered by the separate independent
helper tests. Its compiler permits the known `-Wtype-limits` warning for a
32-bit exponent-length overflow guard that is trivially false on this
64-bit build; all other enabled warnings remain errors.

No full T-board solver run was launched by this build or validation task.
