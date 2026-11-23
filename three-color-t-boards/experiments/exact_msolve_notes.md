# Independent F4 basis backend

The unrestricted ternary count remains unknown. This backend uses msolve's
F4 algorithm with exact sparse linear algebra, then counts the completed
leading ideal with the two independent Python integer counters. A completed
polynomial input or an unfinished F4 round is not a count.

## Provenance and exact arithmetic

The stock msolve 0.11.0-1 package was extracted locally from the configured
official Arch repository. Its archive checksum was verified against the
repository database. The archive, executable hash and package metadata are
in `exact_msolve_tools/package.json`. `exact_msolve_setup.py` reproduces the
local extraction; runtime dependencies come from the earlier local algebra
setup. No system package was installed. A stalled upstream binary download
was explicitly cancelled before this package was used.

The [official documentation](https://github.com/algebraic-solving/msolve/blob/master/README.md)
describes `-g 1` as a leading-ideal export and `-g 2` as a full basis export.
The pinned executable's help and tagged source identify `-l 2` as exact
sparse linear algebra. The runner explicitly supplies `-l 2 -t 1 -r 1 -c 0`:
no probabilistic linear-algebra mode, no variable-order changes, and no
random linear form. The random-seed announcement in the log does not change
the selected exact finite-field algorithm.

Stock msolve computes a machine-integer staircase size after writing even a
`-g 1` export. That is unnecessary here and can fail on a compact ideal with
an enormous quotient. The separately pinned
[source patch and validation](exact_msolve_patched_tools/README.md) return
after the checked prime-field basis export, before staircase enumeration.
The patch rejects a failed basis computation and prints exactly one
`MSOLVE_PRIME_GB_EXPORT_COMPLETE` marker. It does not alter the basis
algorithm. Twelve small stock/patched exports match byte for byte. For 100
independent cubic domains, both versions write the same leading ideal; the
patched version finishes, and both Python counters return
`515377520732011331036461129765621272702107522001 = 3^100`.

This trusts msolve's completed exact basis algorithm. Counting its leading
monomials independently does not independently prove the preceding
Buchberger criterion or ideal membership.

## Model and fixed-prefix extension

The unrestricted input is the ordinary F29 ring with 100 variables, all 100
domains `x_i^3-1`, and all 80 nonconstant geometric Fourier sums. The quotient
dimension is directly the full labeled count: the divisor and symmetry
multiplier are both one. No Boolean reduction is used. The
[actual-file audit](exact_parity_math_msolve_audit.json) independently rebuilt
the placements from centered Cartesian coordinates and checked every input
polynomial.

For a fixed prefix, coefficients can lie in F29². The adapter represents a
genuine quadratic coefficient by an extra ordinary variable `a` and the
equation `a²+a+1=0`. The resulting F29 quotient dimension is twice the
F29² dimension, so it divides by exactly two. When all specialized
coefficients already lie in F29, this extra variable is omitted and the
divisor is one. Colors are `1,a,-a-1`.

The [independent adapter review](exact_msolve_review_notes.md) checked 5,150
polynomials in 39 geometric models, field-degree accounting, strict output
parsing and completion/error paths. It also verified that a rejected rerun
cannot overwrite old artifacts. Both Python counters use arbitrary-size
integers. Only a fresh, complete leading export with matching unique
metadata, successful exit and no diagnostic can reach counting. Patched
runs additionally require exactly one completion marker.

## Completed and incomplete checks

Stock ordinary-ring fixtures give dimensions 3 and 9 for one and two cubic
domains, 6 for the three-root sum-zero fixture, and 0 for the unit ideal.
The ordinary F2 cubic fixture gives dimension 3, confirming that it was not
silently interpreted as a Boolean variable.

The known nine-row six-completion fiber gives F29 quotient dimension 12,
with the auxiliary quadratic variable, and hence exactly six boards. Stock
and patched executions both complete; both integer counters agree. A patched
ten-variable pure-power fixture gives exactly `10^20`, above 64-bit range.
The reduced 21-variable binary algebra trial timed out at 30 wall seconds;
the known binary total 168 was not obtained by that trial.

The first unrestricted F4 trial used at most 256 pairs per matrix, a
90-second solver wall limit, and a 2 GiB address-space cap. The whole Python
pipeline had a separate 180-second/2 GiB guard. It completed the degree-two
and degree-three rounds, then timed out during degree-four matrix
construction: 82.064466 solver CPU seconds and 90.231897 solver wall seconds.
Its basis file is empty, no completion marker or leading JSON exists, and
there is no quotient dimension. The terminal status is `INCOMPLETE_TIMEOUT`.

The run artifacts are `exact_msolve_full_prime29_all.ms`, `.log`, `.json`,
`.outer.log` and `.outer.json`. Input SHA256 is
`4f3610b250e309bb1f5f722c6c621354f8078e0fc91df5e5e860edd323f60b55`.
The later pair-batch-16 trial uses the byte-identical ideal and is recorded
as `exact_msolve_full_prime29_pairs16.*`. It also timed out during degree-four
matrix construction, after 69.161733 CPU / 90.259985 wall seconds, with an
empty basis file and no count. The pair setting is a target, not a strict
cap: boundary pairs sharing the same leading-monomial LCM are kept together.

A characteristic-two trial, `exact_msolve_full_prime2_pairs16.*`, changes
only the input field declaration. Its degree-four matrix had 23,221 rows and
3,337,853 columns. Linear algebra reported 17 new polynomials, but subsequent
growth of the basis monomial hash failed under the 2 GiB cap. The solver
printed an exponent-vector allocation failure followed by a segmentation
fault warning, then exited with signal 11 after 69.641591 CPU / 80.636474 wall
seconds. Core dumps were disabled by the wrapper. The basis file remains
empty; no completion marker or count was produced.

Source inspection located that allocation after linear algebra, when the
implementation reserves and copies every nonpivot column into the separate
basis hash. The advertised `-u` reset option is not read by ordinary
`core_f4` in this pinned version, so a retry changing only that option would
not address the failure. A separate support-only column-import change is
being checked; the original export-only binary and all run artifacts are
preserved.

## Reproduction

After the documented local setup and patched build, use a **fresh** output
prefix (existing artifacts are deliberately not overwritten):

```sh
python3 experiments/exact_algebra_backend_guarded.py --backend msolve \
  --output experiments/exact_msolve_full_prime29_fresh \
  --outer-seconds 180 --outer-memory-mb 2048 -- \
  --prime 29 --seconds 90 --memory-mb 2048 --max-pairs 256 \
  --executable experiments/exact_msolve_patched_tools/msolve \
  --library-dir experiments/exact_algebra_backend_root/usr/lib \
  --require-export-marker
```

`-m` changes the batch size of critical pairs per matrix, not the complete
set of pairs that must be processed. A resource limit never establishes a
zero count. All ten cap fibers in the separate symmetry manifest also remain
uncounted.
