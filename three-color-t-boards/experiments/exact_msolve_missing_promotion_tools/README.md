# Reserve only missing retained monomials

This third preserved msolve build avoids reserving new basis-hash entries for
referenced monomials already present in that hash. It changes only the
retained-column helper introduced by the previous selective-import build.
Previous source trees, binaries and run artifacts remain unchanged.

The concrete trigger is the ordered full F2 trial's second degree-four
promotion: its conservative reservation exhausted the 2 GiB limit before
reporting how many referenced terms were actually new. An earlier completed
round already showed this over-reservation: 95,359 referenced columns caused
a capacity doubling, although only 148 entries were inserted. This patch
does not reduce the working matrix or guarantee that a full count will fit.

## Pinned build

- Upstream: <https://github.com/algebraic-solving/msolve>, tag `v0.11.0`, commit
  `cc044551f8e202d00691990fd3fd0b1226a88ea2`.
- Original archive SHA256:
  `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`.
- Applied predecessor patches, in order: `leading-export-only.patch`
  (`2b109358fc7a77dc70c1570f194c376df68605caa1f4afbce116fa74bfeb99fd`),
  then `retained-column-promotion.patch`
  (`3955ca519da0b32a5e000792d7d36000d45a8971eea8fb56d1e793cd40a0edeb`).
- New incremental patch: `missing-column-reservation.patch`, SHA256
  `c0940b59cd8b6a62d22ee6a7072d6614a9532d82a3b16ca2403fe631fd8b9022`.
- Executable: `msolve`, SHA256
  `1e2111b5e1ef28201f3b2da6bc727d4563569e96b3468ab241433e7d2238a202`.
- Preserved selective-import baseline SHA256:
  `997199fc836584627dc1c6324fc2702a4d900f4cee84d4534acd89f29a068093`.
- Final `src/neogb/hash.c` SHA256:
  `7aa5d271c4a2923dca5a321810e0d13a1ba9e666178e5199c1719d352263db70`.

`source.json` records exact source, patch, compiler, binary and shared-library
provenance. After extracting the pinned archive into a fresh directory and
applying these three patches with `patch -p1`, the build used:

```
./autogen.sh
./configure --disable-shared --enable-static --disable-openmp
make -j1
```

The exact environment is recorded in the manifest: `CFLAGS=-O2 -g0` and the
existing local dependency extraction in `../exact_algebra_backend_root/usr`
for `CPPFLAGS`, `LDFLAGS` and `LD_LIBRARY_PATH`. Build stage wall times were
5.22, 11.20 and 26.61 seconds. Logs and `ldd.txt` are retained. There was no
system installation.

## Algorithm and invariants

The prior support scan still marks every term in every retained nonzero row.
Before growing the basis hash, the helper now looks up each marked symbolic
monomial using the existing `is_contained_in_hash_table` routine. It computes
the hash with the basis table's random weights over the complete exponent
vector. Return values are handled separately: 1 means found, 0 means missing,
and any other result causes a nonzero error exit.

For an existing monomial, the returned exponent-array ID is saved in the
column map and its mask byte becomes 2. This ID remains stable when the hash
grows. No hash bucket position or exponent-data pointer is retained across
enlargement. For a missing monomial the symbolic ID remains unchanged and
the mask remains 1. The helper reserves exactly the number of missing
monomials, then inserts mask-1 columns in ascending original column order.
The existing insertion routine remains unchanged.

Symbolic matrix columns represent distinct exponent vectors. Thus the
missing count equals the number of subsequent new entries; an explicit
postcondition checks this. The selected caller is single-threaded during
promotion, with no concurrent basis insertion between counting and import.
Existing IDs and the order of new IDs match the previous selective helper
exactly. Hash bucket placement can differ because the table may be smaller,
but pending pairs and coefficients refer to monomial IDs, not bucket slots.
The row/coefficients conversion is unchanged.

The previous call-site restrictions remain: ordinary prime-field DRL,
`NO_TRACER`, exact sparse linear algebra (`laopt == 2`), and basis export.
Other callers still use the legacy wrapper. The new helper also rejects
aliased symbolic/basis tables, unequal exponent-vector lengths, invalid
lookup IDs, missing reserved capacity, and a discrepancy between missing
count and actual insertions. Existing row/column/allocation guards remain.
The upstream allocator itself is unchanged; an allocation failure remains an
incomplete/error solver result.

The new pre-growth diagnostic makes the reason for a failed reservation
observable:

```
MSOLVE_PROMOTION_RESERVATION nonpivot=N referenced=R missing=M basis_load=L basis_capacity=C
```

The existing post-import `MSOLVE_PROMOTION_COLUMNS` diagnostic is retained
unchanged. Completed imports must have `missing == inserted`.

## Validation

`validate.py` compares this executable with the preserved selective build
using `-l2 -t1 -r1 -c0 -v2`, separately for leading (`-g1`) and full (`-g2`)
exports. All 16 comparisons passed byte-for-byte: seven small ideals and the
known nine-row prefix with six ternary completions. The latter retains
quotient dimension 12 and extension divisor 2, independently checked by both
Python-bigint staircase implementations. Existing-column overlap is
exercised, and every completed reservation's missing count equals its actual
insertion count. Each solver child had a 2 GiB address-space cap; raw commands,
input/basis hashes, CPU/wall usage and diagnostics are in `validation.json`
and individual artifacts.

`helper_check.py` extracts the actual upstream lookup, insertion and
enlargement/rehash functions, plus the candidate promotion helper, into an
ASan/UBSan harness. All 2,000 deterministic cases passed: 1,428 required hash
growth, 1,942 reused existing columns, and 907 reserved strictly less capacity
than the previous helper. Half force every hash value to collide. The tests
compare every final monomial ID, exponent vector, metadata record and column
map against the conservative reference and verify unchanged row arrays.
An explicit all-reused case retains capacity 8 where the previous helper
would grow to 16; a second case grows while preserving cached existing IDs.

The only arithmetic helper stubbed in that harness is
`generate_short_divmask`, which returns zero: divisibility-mask generation
is not tested. It uses real successful allocation and rehashing, but does
not claim to validate upstream out-of-memory behavior. See `helper_check.c`,
`helper_check.json` and `helper_check.log` for exact extracted-source hashes
and sanitizer commands. The independent review separately checks failure
paths and complete small bases.

No full T-board run was executed during validation.
