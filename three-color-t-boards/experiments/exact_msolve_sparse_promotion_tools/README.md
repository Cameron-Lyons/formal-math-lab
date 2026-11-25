# Retained-column promotion build

This second local msolve 0.11.0 build imports only symbolic monomials used by
the returned nonzero rows into the persistent basis hash. The previous
export-only build in `../exact_msolve_patched_tools` is preserved. This build
has passed the small validation described below; these tests do not compute
the unrestricted T-board count.

The motivation is a specific allocation failure in the unrestricted ordinary
F2 run. Its degree-four matrix had 23,221 rows and 3,337,853 columns. Exact
linear algebra completed and returned 17 new polynomials before the old
conversion attempted to import every nonpivot column. That import reserved
at least 3,314,632 basis-hash slots although most columns might be absent from
the 17 output rows. The failure was in the second hash allocation, after the
working matrix had already fit under the 2 GiB address-space cap. This patch
does not reduce the working symbolic matrix or guarantee that a later round
will fit. The observed `-m16` setting is a pair-batch target and can produce
17 selected pairs. A later [selector audit](../exact_msolve_pair_batch_analysis.md)
documents an offset in the pinned version's LCM boundary loop; no guarantee
that it preserves every complete tie group is made.

## Pinned provenance

- Upstream repository: <https://github.com/algebraic-solving/msolve>
- Tag: `v0.11.0`; commit: `cc044551f8e202d00691990fd3fd0b1226a88ea2`.
- Source archive: `../exact_msolve_patched_tools/msolve-v0.11.0-source.tar.gz`.
- Archive SHA256:
  `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`.
- First applied patch: `../exact_msolve_patched_tools/leading-export-only.patch`,
  SHA256 `2b109358fc7a77dc70c1570f194c376df68605caa1f4afbce116fa74bfeb99fd`.
- Incremental patch: `retained-column-promotion.patch`, SHA256
  `3955ca519da0b32a5e000792d7d36000d45a8971eea8fb56d1e793cd40a0edeb`.
- Executable: `msolve`, SHA256
  `997199fc836584627dc1c6324fc2702a4d900f4cee84d4534acd89f29a068093`.
- Preserved export-only executable SHA256, reconfirmed after building:
  `2d3258dd099a34410b05eadd21dbb38db22b8be0962ab59115d01660652c355d`.

`source.json` records per-file before/after hashes, build environment,
compiler version and runtime-library hashes. `autogen.log`, `configure.log`,
`make.log` and `ldd.txt` retain build output. No system installation was used.

## Scope and preservation argument

The incremental patch changes three files under the pinned source tree:

1. `src/neogb/hash.c` adds a helper that scans every term of every retained
   row `mat->tr[i]`, `i < mat->np`. A byte mask deduplicates referenced
   nonpivot columns. It reserves at most that many new basis slots, then
   imports the marked columns in their original ascending column order.
2. `src/neogb/convert.c` introduces an internal selection flag. The existing
   old-signature wrapper always uses the old all-column import. Coefficient
   pointers, row order, degree calculation and subsequent parallel row
   remapping remain unchanged.
3. `src/neogb/f4.c` enables the selective helper only in `compute_new_elements`
   when `trace_level == NO_TRACER`, `laopt == 2`, `fc > 0`, `nev == 0`, and
   `print_gb > 0`. This is the exact sparse, ordinary prime-field, no-trace,
   DRL basis-export path used here. Other callers, including final reduction
   and tracing/modular paths, retain the old import.

Every column read by the unchanged row conversion has been marked and
mapped first. Every retained coefficient and exponent is preserved. Existing
basis hash IDs remain unchanged, so pending pairs continue to refer to the
same monomials. New IDs can differ because unused monomials are omitted;
the retained insertions still occur in ascending column order. Unreferenced
column-map entries remain symbolic IDs but are never read by the retained-row
conversion. In the selected ordinary path, the symbolic hash is cleaned and
the matrix discarded immediately afterwards.

Tracing paths are deliberately excluded because they can compare hash IDs
across primes with different retained supports. There is no claim that
selective import is valid for such paths.

The helper rejects inconsistent dimensions, missing/empty/oversized retained
rows, out-of-range retained columns, invalid symbolic hashes and failure to
allocate the support mask. It exits nonzero and cannot emit the later basis
completion marker on those failures. Normal valid caller pointers are
assumed. The upstream hash enlarger's unchecked reallocation behavior has
not been changed: allocation failure can still terminate the solver, which
must remain an incomplete/error result. The patch does not make that
allocator failure-safe.

At verbosity 2, each selective import reports:

```
MSOLVE_PROMOTION_COLUMNS nonpivot=N referenced=R inserted=I basis_capacity=C
```

`R` counts distinct referenced symbolic columns; `I` counts new basis-hash
entries after deduplication against the existing basis. Thus `I <= R <= N`.
The allocation reservation uses `R`, a safe worst case, and does not promise
the minimal possible capacity.

## Build and validation

Extract the pinned archive into a fresh directory, then apply the export-only
patch followed by this incremental patch with `patch -p1`. In that source
directory, the recorded commands are:

```
./autogen.sh
./configure --disable-shared --enable-static --disable-openmp
make -j1
```

The exact absolute environment is in `source.json`: `CFLAGS=-O2 -g0`, local
FLINT include/library paths in `CPPFLAGS`/`LDFLAGS`, and
`LD_LIBRARY_PATH=../exact_algebra_backend_root/usr/lib` resolved absolutely.
Configure completed in 11.97 wall seconds and make in 24.57 wall seconds.
The executable dynamically uses the recorded FLINT/GMP/MPFR libraries.

`validate.py` compared the preserved export-only binary and this build with
`-l2 -t1 -r1 -c0 -v2`, separately for `-g1` and `-g2`. All runs used a 2 GiB
address-space cap. Seven small ideals cover cubic domains, mixed equations,
unit and positive-dimensional ideals. The eighth fixture is the independently
known six-completion, nine-row ternary prefix over F29. All **16 complete
leading/full-basis exports were byte-identical**. Finite dimensions were
checked by two independently implemented Python-bigint staircase counters;
the positive-dimensional example was rejected as having no finite bound.

The six-fiber used 20 variables including the quadratic coefficient variable.
Its quotient dimension was 12, giving exactly six boards after the recorded
extension divisor 2. Its leading export SHA256 is
`a75b23d860139a32c1d1e2f4c613bf67f49c649114919bf44560558b4cf2d52c`;
its full-basis export SHA256 is
`c406cfffacd771d97a2fdccff3e47b83c31468fd2fa6e5fc544aaa283d8cb047`.

| Six-fiber export | Baseline CPU / wall seconds | Selective CPU / wall seconds |
| --- | --- | --- |
| Leading monomials (`-g1`) | 1.205 / 1.590 | 1.986 / 2.593 |
| Full basis (`-g2`) | 1.136 / 1.489 | 1.162 / 1.282 |

These one-shot checks establish agreement, not a performance improvement.
The 17 selective rounds in each six-fiber run referenced 2,097 of 2,214
nonpivot-column occurrences and inserted 520 new basis entries. A smaller
mixed-chain fixture includes a round referencing only two of six columns,
so the skipped-column branch is exercised. Raw commands, CPU/wall usage,
hashes and per-round diagnostics are in `validation.json` and the individual
`.ms`, `.basis`, `.log`, `.json` artifacts. The driver refuses to overwrite
existing fixture artifacts.

Independent review additionally extracted the helper into a minimal stubbed
hash-table harness: 5,000 randomized cases plus 12 invalid-input/allocation
cases passed under ASan and UBSan. This checks support mapping, untouched
columns, existing IDs, insertion order, and unchanged row metadata; it does
not test the upstream allocator. The independent files live one directory
above: `exact_msolve_sparse_helper_check.py`,
`exact_msolve_sparse_helper_check.c`, and
`exact_msolve_sparse_helper_results.json`.

The independent reviewer also completed 20 small mixed-ideal comparisons
across characteristics 2, 5, 29, 257 and 65,537. Each selective full basis
agreed with the preserved export-only build and an independently implemented
exact Python Buchberger computation. The report is
`../exact_msolve_sparse_review_results.json`; the reproducible checker is
`../exact_msolve_sparse_review.py`. All passed with the executable hashes
listed above.

No unrestricted T-board solver run was launched by this validation.
