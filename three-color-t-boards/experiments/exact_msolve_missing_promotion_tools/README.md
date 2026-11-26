# Reserve only missing retained monomials

This third preserved msolve build avoids reserving basis-hash slots for referenced monomials that are already in the basis hash. It modifies only the retained-column helper added in the second build. All earlier source trees, binaries, and run artifacts are untouched.

The motivation was the ordered full F2 trial's second degree-4 promotion, where conservative reservation hit the 2-GiB limit before showing how many referenced terms were truly new. An earlier round had already shown the waste: 95,359 referenced columns forced a capacity doubling even though only 148 entries were new. This patch does not shrink the working matrix or guarantee that a full run fits in memory.

## Pinned build

- Upstream: <https://github.com/algebraic-solving/msolve>, tag `v0.11.0`, commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`
- Original archive SHA-256: `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`
- Predecessor patches in order: `leading-export-only.patch` (`2b109358fc7a77dc70c1570f194c376df68605caa1f4afbce116fa74bfeb99fd`), then `retained-column-promotion.patch` (`3955ca519da0b32a5e000792d7d36000d45a8971eea8fb56d1e793cd40a0edeb`)
- New incremental patch: `missing-column-reservation.patch`, SHA-256 `c0940b59cd8b6a62d22ee6a7072d6614a9532d82a3b16ca2403fe631fd8b9022`
- Executable `msolve` SHA-256: `1e2111b5e1ef28201f3b2da6bc727d4563569e96b3468ab241433e7d2238a202`
- Selective-import baseline SHA-256: `997199fc836584627dc1c6324fc2702a4d900f4cee84d4534acd89f29a068093`
- Final `src/neogb/hash.c` SHA-256: `7aa5d271c4a2923dca5a321810e0d13a1ba9e666178e5199c1719d352263db70`

`source.json` records exact source, patch, compiler, binary, and shared-library provenance. After extracting the archive into a fresh directory and applying all three patches with `patch -p1`, the build commands were:

```
./autogen.sh
./configure --disable-shared --enable-static --disable-openmp
make -j1
```

The build used `CFLAGS=-O2 -g0` and the local dependency tree in `../exact_algebra_backend_root/usr` for `CPPFLAGS`, `LDFLAGS`, and `LD_LIBRARY_PATH`. Stage wall times were 5.22, 11.20, and 26.61 seconds. Logs and `ldd.txt` are saved, and no system install was used.

## Algorithm and invariants

The support scan still marks every term appearing in retained nonzero rows. Before growing the basis hash, the helper now checks each marked symbolic monomial with `is_contained_in_hash_table`, using the basis table's random weights across the full exponent vector. Return values are checked explicitly: `1` means found, `0` means missing, and anything else triggers a nonzero error exit.

- If a monomial is already present, its basis exponent-array ID is stored in the column map and its mask byte is set to `2`. That ID survives hash growth, and no bucket slot or exponent pointer is cached across enlargement.
- If a monomial is missing, its symbolic ID stays in the column map and its mask byte stays `1`. The helper reserves space only for the missing count, then inserts mask-1 columns in ascending original column order using the unchanged insertion routine.

Because symbolic matrix columns represent distinct exponent vectors, the missing count equals the number of new basis entries; an explicit postcondition checks this. Promotion runs single-threaded with no concurrent basis insertions between counting and import. Existing IDs and new ID order match the second build exactly. Bucket slots can differ when the table stays smaller, but pending pairs and coefficients reference monomial IDs rather than bucket slots, and row/coefficient conversion is unchanged.

The existing call-site guards stay in place: ordinary prime-field DRL, `NO_TRACER`, exact sparse linear algebra (`laopt == 2`), and basis export. Other callers keep the legacy wrapper. The helper also rejects aliased symbolic/basis tables, mismatched exponent-vector lengths, invalid lookup IDs, insufficient reserved capacity, and any mismatch between missing count and actual insertions. All existing row, column, and allocation checks remain, while the upstream allocator itself stays unchanged (so an allocation failure still ends the run as incomplete/error).

A new pre-growth diagnostic logs each reservation before allocation:

```
MSOLVE_PROMOTION_RESERVATION nonpivot=N referenced=R missing=M basis_load=L basis_capacity=C
```

The existing post-import `MSOLVE_PROMOTION_COLUMNS` line stays unchanged, and every completed import must satisfy `missing == inserted`.

## Validation

- `validate.py` and `validation.json`: 16 byte-for-byte comparisons against the second build using `-l2 -t1 -r1 -c0 -v2` for both `-g1` and `-g2` under a 2-GiB cap. Covers 7 small ideals and the nine-row six-completion prefix (quotient dimension 12, extension divisor 2, giving 6 boards across both Python-bigint staircase counters). Existing-column overlap is exercised and every completed reservation satisfies `missing == inserted`.
- `helper_check.py`, `helper_check.c`, `helper_check.json`, `helper_check.log`: extracts the upstream lookup, insertion, and enlargement/rehash routines plus the candidate helper into an ASan/UBSan harness. All 2,000 deterministic cases pass (1,428 needed growth, 1,942 reused existing columns, 907 reserved strictly less capacity than build 2, half forced all hashes to collide). Every final monomial ID, exponent vector, metadata record, column map, and row array matches the conservative reference. Specific edge cases confirm an all-reused import stays at capacity 8 instead of growing to 16, and growth preserves cached existing IDs.

The harness stubs only `generate_short_divmask` (returning 0), so divisibility-mask generation is untested there, and it runs real successful allocations rather than testing upstream OOM behavior. Independent review separately tests failure paths and complete small bases. No full T-board run was executed during validation.
