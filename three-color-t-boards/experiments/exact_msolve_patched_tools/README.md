# msolve build that stops after prime-field basis export

This local build leaves all Gröbner-basis math unchanged. It checks the finished F4 call for errors, writes the basis using the existing exporter, prints `MSOLVE_PRIME_GB_EXPORT_COMPLETE`, and returns before enumerating standard monomials. The early return applies only to prime-field `-g 1` and `-g 2` requests. No T-board count was run during build validation.

Executable: `experiments/exact_msolve_patched_tools/msolve`. Pass it to the adapter with:

```sh
--executable experiments/exact_msolve_patched_tools/msolve --library-dir experiments/exact_algebra_backend_root/usr/lib --require-export-marker
```

Exact sparse, single-thread invocation:

```sh
msolve -f INPUT.ms -o OUTPUT.basis -g 1 -l 2 -t 1 -r 1 -c 0 -v 2
```

The input file's second line sets the characteristic. `-l 2` selects exact sparse linear algebra (modes 42 and 44 are probabilistic), `-g 1` exports the leading ideal, and `-g 2` exports the reduced basis, as documented in the tagged [CLI source](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/msolve/main.c). A valid leading export must match the input field, variable order, basis length, and closing list terminator; neither exit status 0 nor the completion marker alone is enough for a count.

## Why the patch is needed

In the tagged [solver source](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/msolve/msolve.c), `initial_modular_step` runs F4, writes and closes the basis file, and then calls `monomial_basis` even when `-g 1` was requested (skipping only the later FGLM step). That enumeration stores dimension in a machine `long` and can exhaust memory after a compact basis is already on disk.

This patch returns right after the export, leaving dimension variables at their unknown sentinels rather than reporting zero or an internal machine integer. Counting happens externally with arbitrary-precision Python integers, and the caller already handles a null staircase when basis output is requested.

In the [F4 implementation](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/neogb/f4.c), F4 returns only after finishing its pair loop, pruning redundant elements, and reducing the final basis. The patch rejects any nonzero F4 error or null basis before exporting, and prints and flushes the completion marker only after the [writer](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/msolve/iofiles.c) closes the output file and returns.

The input parser allocates a 1-GiB line buffer at lines 1027-1028, which `get_data_from_file` frees before `core_msolve` begins, so it does not eat address space during F4. No parser change was made. An initial 512-MiB validation cap failed inside that stock parser; all comparisons below use the standard 2-GiB cap.

## Provenance and build

`source.json` records the exact source URL, tag, commit, archive hash, patch hash, original/patched source hashes, build commands and environment, compiler version, executable hash, and resolved runtime-library hashes.

- Upstream tag: `v0.11.0`, commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`
- Source archive SHA-256: `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`
- Patch `leading-export-only.patch` SHA-256: `2b109358fc7a77dc70c1570f194c376df68605caa1f4afbce116fa74bfeb99fd`
- Built executable SHA-256: `2d3258dd099a34410b05eadd21dbb38db22b8be0962ab59115d01660652c355d`

Build steps were `./autogen.sh`, `./configure --disable-shared --enable-static --disable-openmp`, and `make -j1`, using the local FLINT headers/libraries, `CFLAGS=-O2 -g0`, and a local-library rpath. Internal msolve libraries are linked statically while FLINT, MPFR, and GMP remain dynamic. No system package was installed. Build logs are saved in `autogen.log`, `configure.log`, `make.log`, and `ldd.txt`.

## Validation

`python experiments/exact_msolve_patched_tools/validate.py` runs 12 byte-for-byte stock-vs-patched comparisons across 6 ideals (both `-g 1` and `-g 2`): one and two cubic domains, the three-root sum equation, a mixed product constraint, the unit ideal, and a positive-dimensional ideal. All 12 match, and the finite-dimensional counter properly rejects the positive-dimensional ideal.

For 100 independent cubic domains, both Python counters return the exact quotient dimension:

```text
3^100 = 515377520732011331036461129765621272702107522001
```

Under a 2-GiB address-space cap, the patched binary finished with exit 0 and one completion marker in 0.005751 CPU seconds (0.009538 wall seconds). Stock msolve (with an added 2-second wall guard) wrote the identical leading ideal, then exited 1 with `Issue with realloc` after 0.430302 CPU seconds (0.514296 wall seconds) during post-export enumeration.

Commands, raw outputs, basis hashes, and timings are saved in `validation.json` and the per-fixture `.ms`, `.basis`, and `.log` files. These are small arithmetic fixtures and do not yield an unrestricted T-board count.
