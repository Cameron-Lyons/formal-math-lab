# Rounded exponent storage for basis promotion

This fourth preserved build grows basis exponent storage to the needed entry count rounded up to a multiple of 64K slots, while keeping hash buckets as a separate power-of-two allocation. It applies only to the guarded ordinary, exact, non-tracing F4 promotion path. The legacy grower and all three earlier builds stay unchanged.

The motivating failure had basis load 2,078,104 with 55,218 missing monomials. The old grower doubled capacity from 2,097,152 to 4,194,304 slots. This build instead requests 2,162,688 exponent slots and 8,388,608 buckets: for the 100-variable layout, principal basis arrays drop from 936 MiB to 498.125 MiB, saving 437.875 MiB at that boundary. This calculation excludes matrix storage, other hash tables, and reallocation peaks, so it does not guarantee a full solve fits under 2 GiB or finishes.

## Pinned provenance

- Upstream: <https://github.com/algebraic-solving/msolve>, `v0.11.0`, commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`
- Original archive SHA-256: `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`
- Patches: apply the three predecessor patches in `source.json`, then `rounded-promotion-capacity.patch`, SHA-256 `d569538b42f58dbf7160621891918cddc9496347a8229f350350eb5977539461`
- Executable `msolve` SHA-256: `cebd842aa617f09725a1f5429ebc822da238563f142b14993cccb85312d1874c`
- Missing-only baseline SHA-256: `1e2111b5e1ef28201f3b2da6bc727d4563569e96b3468ab241433e7d2238a202`
- Final `src/neogb/hash.c` SHA-256: `81104b9e535ff3cc057611238a9987c718099f0ba2431d38c734d667e662aefd`

`source.json` records all archive, patch, file, and library hashes plus the build environment (`CFLAGS=-O2 -g0`, local dependencies under `../exact_algebra_backend_root/usr`, no system install). Build commands were `./autogen.sh`, `./configure --disable-shared --enable-static --disable-openmp`, and `make -j1`, taking 5.86, 12.45, and 26.05 wall seconds.

## Reservation and compatibility

`reserve_basis_hash_table_for_promotion` takes the exact missing count from build 3 and reserves `eld + missing + 1`, rounded up to a multiple of 65,536. The extra spare slot satisfies legacy checks that grow when `eld == esz - 1`, preventing an exact-fit promotion from leaving `eld == esz`.

The helper checks load addition, rounding bounds, and every byte-size multiplication for overflow. Exponent capacity is capped at `2^30` and buckets at `2^31` to avoid a legacy reset routine that narrows `hsz` to 32 bits at `2^32`. Buckets stay a nonzero power of two at least twice the exponent capacity and only grow when needed to keep that invariant.

Metadata, exponent-pointer, and exponent-data reallocations all write through checked temporary pointers. Every `ev` pointer (including slot 0) is rebuilt after the data block moves. When buckets grow, the bucket array is cleared and all existing entry IDs are reinserted using their saved hash values. IDs, exponents, coefficients, pending-pair references, and insertion order never change. Any allocation error or unsupported state exits nonzero before the export marker can print. All other callers keep the untouched legacy grower.

Across copy, reset, clean, and legacy growth, `esz` is used only as a linear array bound while `hsz` is the bit mask (see `../exact_msolve_capacity_analysis.md` and `.json`). Because the old summary stats print `ceil(log2(max_esz))` as `2^k`, that line becomes an upper bound; check the new diagnostic for exact figures:

```
MSOLVE_PROMOTION_CAPACITY_REQUEST required_with_spare=R exponent_old=A exponent_new=B buckets_old=C buckets_new=D
```

This line logs the request before allocation and does not mean the allocation succeeded. The existing post-import diagnostic and final export marker keep their usual meanings.

## Completed validation

- **Build comparisons (`validation.json`)**: All 16 `-g1` / `-g2` runs (7 small ideals plus the six-completion ternary prefix) match build 3 byte-for-byte. Both bigint counters confirm quotient dimension 12 and 6 boards for the prefix. Passing `-s4` forces a tiny initial hash and triggers two rounded promotions.
- **Independent basis review (`../exact_msolve_rounded_review_results.json`)**: 25 complete small bases across 5 prime characteristics (including characteristic 2) match build 3 and an independent Python Buchberger solver, exercising 10 rounded-growth events.
- **Independent ASan/UBSan helper review (`../exact_msolve_rounded_capacity_results.json`)**: Passed 3 real reallocation/collision cases (including non-power-of-two capacity 196,608 and the unchanged-bucket branch), 4 injected reallocation failures, 7 independent capacity plans, and 13 invalid-layout/overflow rejections.
- **Upstream compatibility harness (`compatibility_check.py`, `compatibility_check.json`)**: Runs actual upstream lookup, insertion, copy, clean, reinitialize, secondary-table init, reset/reinsert, and legacy growth under ASan/UBSan in normal and forced-collision modes. Capacity 196,608 grows via the legacy grower to 393,216 with every ID and exponent intact; copies, secondary tables, reset renumbering, and the exact-boundary spare-slot case all pass cleanly.

The compatibility harness stubs only divisibility-mask generation and timing helpers (allocation failures are tested in the independent helper harness). Its build flags allow the known `-Wtype-limits` warning on a 32-bit length guard that is always false on 64-bit builds, while keeping all other warnings as errors. No full T-board run was executed during validation.
