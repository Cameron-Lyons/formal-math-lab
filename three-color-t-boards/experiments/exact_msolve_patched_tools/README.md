# msolve build that stops after prime-field basis export

This separate local build changes no Gröbner-basis mathematics. It checks the completed F4 call for errors, exports the basis using the existing writer, emits `MSOLVE_PRIME_GB_EXPORT_COMPLETE`, and returns before enumerating the standard monomials. The early return applies only to prime-field `-g 1` and `-g 2` requests. No T-board counting run was performed during this build validation.

The executable is `experiments/exact_msolve_patched_tools/msolve`. Root's adapter can use it with:

```sh
--executable experiments/exact_msolve_patched_tools/msolve --library-dir experiments/exact_algebra_backend_root/usr/lib --require-export-marker
```

The exact sparse, single-thread command is:

```sh
msolve -f INPUT.ms -o OUTPUT.basis -g 1 -l 2 -t 1 -r 1 -c 0 -v 2
```

The characteristic is specified on the input file's second line. `-l 2` uses exact sparse linear algebra; modes 42 and 44 are probabilistic. `-g 1` exports the leading ideal, while `-g 2` exports the reduced basis. This is documented in the tagged [CLI source](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/msolve/main.c). The full leading export must match the input field, variable order, basis length and final list terminator. Neither an exit status nor the completion marker alone establishes a valid count.

## Why the patch is necessary

In the tagged [solver source](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/msolve/msolve.c), `initial_modular_step` calls F4, exports and closes the basis file, then calls `monomial_basis` even when `-g 1` was requested. Only the later FGLM stage is skipped. That enumeration stores its dimension in a machine `long` and can consume enormous memory after a compact basis has already been computed.

The patch stops immediately after the export. It leaves dimension variables at their existing unknown sentinels; it does not report zero or an internal machine-integer dimension. Counting is performed externally with Python integers. The existing caller already handles a null staircase when basis printing is requested.

The [F4 implementation](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/neogb/f4.c) returns after completing its pair loop, removing redundant elements and reducing the final basis. The patch explicitly rejects a nonzero F4 error or null basis before export. Its marker is emitted and flushed only after the existing basis writer returns. The [writer](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/msolve/iofiles.c) closes the output file before returning.

The same input-parser source allocates a 1 GiB line buffer at lines 1027–1028. `get_data_from_file` frees that buffer before it returns and before `core_msolve` starts. It therefore does not consume address space during F4. No parser change was made. An initial 512 MiB validation guard failed in the stock parser; all reported comparisons below use the existing 2 GiB limit.

## Provenance and build

`source.json` records the exact source URL, tag, commit, archive hash, patch hash, original/patched source hashes, build commands/environment, compiler version, executable hash and resolved runtime-library hashes. The source tag is v0.11.0, commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`.

The source archive SHA256 is `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`.

The exact change is saved in `leading-export-only.patch`, SHA256 `2b109358fc7a77dc70c1570f194c376df68605caa1f4afbce116fa74bfeb99fd`.

The built executable SHA256 is `2d3258dd099a34410b05eadd21dbb38db22b8be0962ab59115d01660652c355d`.

Build steps were `./autogen.sh`, `./configure --disable-shared --enable-static --disable-openmp`, and `make -j1`, using the previously extracted local FLINT headers/libraries, `CFLAGS=-O2 -g0`, and a local-library rpath. Internal msolve libraries are static; FLINT, MPFR and GMP remain dynamic. No system package installation was performed. Build output is retained in `autogen.log`, `configure.log`, `make.log`, and `ldd.txt`.

## Validation

`python experiments/exact_msolve_patched_tools/validate.py` performs twelve byte-for-byte stock/patched export comparisons: six ideals, each with both `-g 1` and `-g 2`. The fixtures cover one and two cubic domains, the three-root sum equation, a mixed product constraint, the unit ideal, and a positive-dimensional ideal. Every comparison passed. The positive-dimensional leading ideal is correctly rejected by finite-dimensional monomial counting.

For 100 independent cubic domains, both Python counters establish the exact quotient dimension

```text
3^100 = 515377520732011331036461129765621272702107522001
```

The patched process completed with one marker and exit 0 in 0.005751 CPU seconds and 0.009538 wall seconds. The stock process produced the identical leading export, then exited 1 with `Issue with realloc` in 0.430302 CPU seconds and 0.514296 wall seconds. Both had a 2 GiB address-space limit; the stock comparison also had a two-second wall guard. Its failure is a post-export enumeration failure, not zero solutions.

All commands, raw outputs, basis hashes and timings are recorded in `validation.json` and the per-fixture `.ms`, `.basis`, and `.log` files. These are arithmetic fixtures, not an unrestricted T-board count.
