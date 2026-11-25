# Serial exact F2 matrix kernel

This fifth preserved build replaces one ordinary characteristic-two F4 linear
algebra path with exact XOR reduction. It keeps the existing input ideal,
monomial ordering, coefficient arrays at the solver boundary, hash tables,
pair selection, final reduction and export-completion protocol. It does not
add Boolean identities to polynomial variables. In particular, a domain
`x^3+1` still contributes quotient dimension three over F2.

The purpose is to reduce the transient matrix memory that caused the prior
full run's confirmed null output-row allocation. No full board solve was
launched as part of this build or its validation.

## Pinned build

Upstream is `algebraic-solving/msolve`, tag `v0.11.0`, commit
`cc044551f8e202d00691990fd3fd0b1226a88ea2`. The original archive SHA256 is
`0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`.
The four predecessor patches and their hashes are recorded in `source.json`.
All four previous source trees, binaries and results are preserved.

The additional patch is `serial-f2-bitset.patch`, SHA256
`3868e06ffa3fba3f1ff30aab9693070489fdc533a683df6e8e6d8ad7c92b3a8b`.
It adds `src/neogb/la_ff_2_bitset.c` and changes only the dispatch within
`exact_sparse_linear_algebra_ff_8` in `src/neogb/la_ff_8.c`.

Frozen executable `msolve` has SHA256
`78e65a3c746a036d12ac67d8c332a9afd2101746eee3b850d4a2ecb5e696f502`.
The new kernel source has SHA256
`194f90bf81adf33cbc006933367056cffce4c2be2fa9210886596b89593928eb`;
the modified caller source has SHA256
`1f949f50b071ab0a249d225012d14c2b996f4f21a5acac25ad3ed9b195f8cffc`.

The recorded build uses `CFLAGS=-O2 -g0`, the existing headers/libraries in
`../exact_algebra_backend_root/usr`, and the same commands as the fourth
build: `./autogen.sh`, `./configure --disable-shared --enable-static
--disable-openmp`, `make -j1`. Exact paths, environment, commands and timings
are in `source.json`. No system installation is required.

## Scope and row invariants

The new dispatch requires every one of:

- `fc == 2`, `laopt == 2`, `nthrds == 1`;
- `trace_level == NO_TRACER`, `nf == 0`;
- no final-reduction step, no elimination block, and `print_gb > 0`.

Every other mode calls the unchanged generic kernel. The new routine repeats
these guards and checks the ordinary matrix layout: `nru == ncl`, and old
pivot row `i` has leading column `i`. Sparse input rows have a nonempty
support, a valid coefficient index, coefficient one at each entry, no
duplicate column, and every tail column is larger than the first column.
The tails may be arbitrarily permuted. This is necessary because the
upstream converter partitions columns into known and unknown pivots without
sorting each row's tail (`convert.c`, comment beginning at line 403 in the
fourth source).

The first draft incorrectly required sorted tails. The first integrated
root-sum test rejected that valid layout with a nonzero exit before any
completion marker. Its binary and logs are preserved as
`msolve-initial-order-check` and `initial_order_check/`. The frozen candidate
contains the corrected check. No unsuccessful result was interpreted as a
count.

## Exactness argument

For coefficient field F2, addition and subtraction are XOR and every
nonzero coefficient is one. A packed bit at position `c` therefore represents
exactly the coefficient of column `c`.

Known upper rows remain sparse. For each lower row in the original order,
the routine copies its support into an initially zero bitset and scans set
columns from left to right. A known old pivot is applied by toggling its
support. A previously created new pivot is applied by wordwise XOR.
Reducers have no nonzero column before their leading column, so applying
one cannot change an earlier column. Columns with no pivot are retained.
After the scan, either the vector is zero or its first nonzero column is a
new pivot. Each operation adds a row already in the current row space;
adjoining this nonzero remainder preserves the combined row space and
increases rank by one. No random choices or incomplete pivot tests occur.

All new rows have zero entries in the old pivot columns. Sorting new pivots
by decreasing leading column and clearing each larger pivot produces the
unique reduced row basis of this residual right-block space. Already
interreduced rows have zero coefficients at every other larger pivot, so a
later XOR does not reintroduce a cleared pivot. Outputs have sorted supports,
coefficient one throughout, and decreasing leading-column order, matching
the serial generic kernel's contract. `BINDEX`, `MULT` and the original
lower-row coefficient slot are retained. `DEG` is initialized to zero and is
overwritten by the existing matrix-to-basis conversion, which computes it
from the leading monomial.

This gives the same new reduced polynomials as the serial generic path.
Their conventional representation is then handed to the unchanged basis
insertion and pending-pair update code. Final basis interreduction also
remains on the original kernel.

## Ownership and allocation audit

| Object | Handling |
| --- | --- |
| Input upper/lower coefficient arrays | Borrowed from `bs`/`tbr`; read for validation, never changed or freed. |
| Input lower sparse row arrays | Copied into the workspace, then freed exactly once and their `mat->tr` slots cleared. |
| Input upper sparse row arrays | Needed during forward reduction; freed exactly once afterwards and `mat->rr` slots cleared. |
| Packed workspace/new pivots | Owned by the new routine. A nonzero workspace transfers into a pivot; a fresh zero workspace is allocated. All are freed before return. |
| Matrix pointer containers | Old `mat->tr` and `mat->cf_8` containers are freed; new containers are sized by output count/lower-row count. The `mat->rr` container remains for existing `clear_matrix`. |
| Output sparse rows and coefficient arrays | Fresh conventional allocations. Ownership transfers through the unchanged matrix-to-basis conversion; `clear_matrix` later frees only pointer containers. |

The obsolete upper sparse rows are freed before any new sparse output row
is allocated. New pivots are packed through both forward elimination and
interreduction; sparse output is materialized once. No full-size pointer
table indexed by all matrix columns is allocated. Every new allocation
checks size arithmetic and allocation success, exiting nonzero on failure.
The completion marker is emitted only much later by the existing export
patch, so such failure cannot attest a completed basis.

The generic kernel materializes sparse pivots during forward reduction and
again during interreduction. It frees each old self-row before replacing it;
this patch does not rely on a claim that two complete sparse output sets
coexist. It removes the coexistence of the first sparse output set with all
old reducer rows, and avoids repeated sparse materialization.

## Memory scope

At the measured matrix width 2,626,958, a bitset occupies 328,376 bytes
(0.3132 MiB), compared with 21,015,664 bytes (20.0421 MiB) for one generic
`int64_t` workspace. The generic full-column pivot-pointer table is another
20.0421 MiB. Seventeen packed new rows occupy 5.3238 MiB; thirty-three occupy
10.3344 MiB. These row counts are illustrative, not a measurement of the
failed allocation's support size or of an unexecuted new full run.

An ordinary sparse output needs approximately `5*k + 24` bytes for `k`
nonzero terms: four-byte column indices and one-byte coefficients plus six
metadata words. A bitset is smaller once support exceeds about 2.5% of the
column count. Old matrix rows remain sparse; the measured complete matrix
density was only about 0.13%. Packing the entire old matrix would waste memory.

The final sparse basis and both monomial hash tables still exist. The old
final-reduction path may still require substantial memory. This patch does
not guarantee that a full run fits under 2 GiB or completes promptly. A
linear scan of the small new-pivot list favors transparent semantics over
additional indexing machinery; its large-instance CPU behavior is untested.

## Validation

`validate.py` / `validation.json` record 18 completed leading/full-basis
comparisons, all byte-identical to the fourth build: seven small ordinary
F2 ideals, the known six-completion F2 prefix, and the same prefix over F29
as an old-kernel regression. Both independent bigint monomial counters give
quotient dimension 12 for either prefix, and the shared extension-variable
factor two gives six boards. F2 single/pair cubic domains retain dimensions
three/nine; the three-root sum has dimension six. Positive-dimensional
input is not reported as a finite count. Kernel diagnostics confirm that
the mixed-chain and F2 prefix cases enter the new path, while F29 does not.

`mode_validation.py` / `mode_validation.json` add four completed full-basis
comparisons for exact sparse-dense option one, requested thread count two,
an elimination block, and characteristic five. Every export is byte-identical
to the fourth build, with no new-kernel diagnostic. These builds have OpenMP
disabled; the thread-count test checks dispatch, not parallel execution.

Independent review passed against the frozen executable and kernel hashes:

- `../exact_msolve_f2_matrix_review_results.json`: the actual included C
  source under ASan/UBSan agrees with an independent Python matrix oracle on
  1,039 matrices and 11,594 output pivots, including 961 unsorted-tail cases
  and 57 zero-output cases. Ownership, original coefficient slots and other
  metadata are checked. Nineteen injected allocation failures and sixteen
  invalid-mode/input cases fail nonzero. No sanitizer findings were reported.
- `../exact_msolve_f2_basis_review_results.json`: twelve distinct complete F2
  ideals yield 24 baseline/candidate bases that are byte-identical and agree
  with an independent Python Buchberger calculation. Thirty-three actual
  bitset rounds were exercised. Fixtures include ordinary cubic quotient
  dimension 27 and a nonradical ideal of multiplicity six.

The reviewer retained an initial baseline failure under a 1 GiB address-space
cap. Repeating at the established 2 GiB cap succeeds; it is not a candidate
regression or a completed basis result. All owner and reviewer processes are
terminal. No full T-board computation has been run with this build by either
validation task.
