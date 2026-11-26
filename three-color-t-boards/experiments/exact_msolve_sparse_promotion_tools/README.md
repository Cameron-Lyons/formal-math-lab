# Retained-column promotion build

This second local msolve 0.11.0 build imports only the symbolic monomials that actually appear in returned nonzero rows into the persistent basis hash. The first export-only build in `../exact_msolve_patched_tools` stays untouched. Small-fixture validation passes below; none of these tests computes the unrestricted T-board count.

The change addresses an allocation failure in the unrestricted ordinary F2 run: its degree-4 matrix had 23,221 rows and 3,337,853 columns, and exact linear algebra finished with 17 new polynomials before the old conversion tried to import all nonpivot columns (reserving at least 3,314,632 basis-hash slots even though most columns might be absent from those 17 rows). The crash hit the second hash allocation after the working matrix had already fit under the 2-GiB cap. This patch does not shrink the working matrix or guarantee that later rounds fit. Note that `-m16` is a pair-batch target that can select 17 pairs; a later [selector audit](../exact_msolve_pair_batch_analysis.md) documented an offset in the upstream LCM tie loop, so full tie preservation is not guaranteed.

## Pinned provenance

- Upstream repository: <https://github.com/algebraic-solving/msolve>
- Tag: `v0.11.0`; commit: `cc044551f8e202d00691990fd3fd0b1226a88ea2`
- Source archive: `../exact_msolve_patched_tools/msolve-v0.11.0-source.tar.gz`, SHA-256 `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`
- First patch: `../exact_msolve_patched_tools/leading-export-only.patch`, SHA-256 `2b109358fc7a77dc70c1570f194c376df68605caa1f4afbce116fa74bfeb99fd`
- Incremental patch: `retained-column-promotion.patch`, SHA-256 `3955ca519da0b32a5e000792d7d36000d45a8971eea8fb56d1e793cd40a0edeb`
- Executable `msolve` SHA-256: `997199fc836584627dc1c6324fc2702a4d900f4cee84d4534acd89f29a068093`
- Preserved export-only executable SHA-256 (rechecked after building): `2d3258dd099a34410b05eadd21dbb38db22b8be0962ab59115d01660652c355d`

`source.json` records per-file before/after hashes, build environment, compiler version, and runtime-library hashes. Build logs are in `autogen.log`, `configure.log`, `make.log`, and `ldd.txt`. No system install was used.

## Scope and correctness

The incremental patch edits three files:

1. `src/neogb/hash.c`: adds a helper that scans every term of every retained row `mat->tr[i]` (`i < mat->np`), marks referenced nonpivot columns in a byte mask, reserves at most that many new basis slots, and imports marked columns in ascending column order.
2. `src/neogb/convert.c`: adds an internal selection flag while keeping the existing wrapper on the old all-column import. Coefficient pointers, row order, degree calculation, and parallel row remapping stay unchanged.
3. `src/neogb/f4.c`: turns on selective import only inside `compute_new_elements` when `trace_level == NO_TRACER`, `laopt == 2`, `fc > 0`, `nev == 0`, and `print_gb > 0` (exact sparse, prime-field, no-trace DRL basis export). Final reduction, tracing, and modular callers keep the old path.

Every column read by row conversion is mapped first, so every retained coefficient and exponent is exact. Existing basis IDs stay unchanged, keeping pending pairs valid. New IDs can differ numerically because unused monomials are skipped, though retained insertions stay in ascending column order. Unreferenced `hcm` entries keep symbolic IDs and are never read by retained-row conversion; right after conversion, the symbolic hash is cleared and the matrix is freed.

Tracing paths are excluded because they compare hash IDs across primes whose retained supports can differ; selective import is not claimed to be safe for tracing.

The helper rejects inconsistent dimensions, missing/empty/oversized retained rows, out-of-range columns, invalid symbolic hashes, and mask-allocation failures, exiting nonzero before the export marker can run. The upstream hash enlarger's unchecked reallocation behavior is untouched, so an allocation failure can still crash the solver and leave the run incomplete.

At verbosity 2, each selective import logs:

```
MSOLVE_PROMOTION_COLUMNS nonpivot=N referenced=R inserted=I basis_capacity=C
```

Here `R` is the number of distinct referenced symbolic columns and `I` is the number of genuinely new basis entries after deduplication (`I <= R <= N`). Reservation uses `R` as a safe upper bound rather than the minimal possible capacity.

## Build and validation

Extract the pinned archive into a fresh directory, apply the export-only patch and then this incremental patch with `patch -p1`, and run:

```
./autogen.sh
./configure --disable-shared --enable-static --disable-openmp
make -j1
```

The exact absolute environment is in `source.json`: `CFLAGS=-O2 -g0`, local FLINT paths in `CPPFLAGS`/`LDFLAGS`, and `LD_LIBRARY_PATH=../exact_algebra_backend_root/usr/lib`. Configure took 11.97 wall seconds and `make` took 24.57 wall seconds; FLINT, GMP, and MPFR link dynamically.

`validate.py` ran 16 comparisons (`-l2 -t1 -r1 -c0 -v2`, `-g1` and `-g2`, 2-GiB cap) against the export-only build across 7 small ideals (cubic domains, mixed equations, unit and positive-dimensional ideals) plus the known six-completion nine-row ternary prefix over F29. All 16 exports match byte-for-byte. Both independent Python-bigint staircase counters verified every finite dimension and rejected the positive-dimensional fixture.

For the nine-row fiber (20 variables including the quadratic extension variable), both counters gave quotient dimension 12 and 6 boards after dividing by 2 (leading export SHA-256 `a75b23d860139a32c1d1e2f4c613bf67f49c649114919bf44560558b4cf2d52c`; full-basis SHA-256 `c406cfffacd771d97a2fdccff3e47b83c31468fd2fa6e5fc544aaa283d8cb047`):

| Six-fiber export | Baseline CPU / wall seconds | Selective CPU / wall seconds |
| --- | --- | --- |
| Leading monomials (`-g1`) | 1.205 / 1.590 | 1.986 / 2.593 |
| Full basis (`-g2`) | 1.136 / 1.489 | 1.162 / 1.282 |

These one-shot runs verify exact agreement rather than speed. Across 17 selective rounds, the six-fiber run referenced 2,097 of 2,214 nonpivot-column occurrences and inserted 520 new basis entries, while a smaller mixed-chain fixture exercised a round referencing only 2 of 6 columns. All logs, timings, and hashes are in `validation.json` and per-fixture files; the driver refuses to overwrite existing outputs.

Independent review added two test suites against the exact frozen executables above:

- `../exact_msolve_sparse_helper_check.py`, `../exact_msolve_sparse_helper_check.c`, and `../exact_msolve_sparse_helper_results.json`: ASan/UBSan tests on the extracted helper with a stubbed hash table (5,000 randomized cases plus 12 invalid-input/allocation rejections), checking mapping, untouched columns, existing IDs, insertion order, and row metadata (without testing the upstream allocator).
- `../exact_msolve_sparse_review.py` and `../exact_msolve_sparse_review_results.json`: 20 small mixed-ideal comparisons across characteristics 2, 5, 29, 257, and 65,537, all matching both the export-only binary and an independent Python Buchberger solver.

No unrestricted T-board run was executed during validation.
