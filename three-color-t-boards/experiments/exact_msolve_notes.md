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
not address the failure.

A separate [support-only column-import build](exact_msolve_sparse_promotion_tools/README.md)
preserves the original binary and imports only columns used by retained
rows. Its [independent review](exact_msolve_sparse_review_notes.md) compared
25 completed bases with both the previous executable and an independent
Buchberger implementation, including cases that actually skip columns.
The mapping helper also passed 5,000 randomized cases and 12 failure cases
under address and undefined-behavior sanitizers.

The unrestricted retry `exact_msolve_full_prime2_sparse_promotion.*` still
failed while growing the basis hash, after 74.761294 CPU / 91.023190 wall
seconds. It used the byte-identical characteristic-two input, the same
2 GiB cap and pair-batch target 16. Earlier rounds imported fewer columns,
but the degree-four round again exhausted memory before exporting a basis.
There is no completion marker or count.

## Dispersed elimination order

The default variable order makes the four unary linear equations pivot on
original cells `0,1,2,3`, which all occur together in the top T. The new
`--pivot-order` option puts cells `0,81,90,99` first. Every T contains at most
one of these cells, so substituting the four linear expressions avoids
products involving several eliminated cells in one placement.

The [independent ordering audit](exact_parity_math_pivot_audit.md) parses
the generated inputs at characteristics 2 and 29 and undoes the permutation.
Every polynomial then agrees with both the original input and independently
reconstructed geometry. All 100 ordinary cubic domains and all 80 moments
remain present. This is a ring isomorphism, with no count multiplier or
divisor. Metadata records the original cell for each variable. A coefficient
extension variable, when required for a fixed prefix, stays last.

The reordered known nine-row fiber, `exact_msolve_pivot_fiber_six.*`,
completed in characteristic two: both counters returned quotient dimension
12, hence six boards after the recorded coefficient-extension divisor two.
This checks a fixed fiber and does not supply an unrestricted count.

The unrestricted reordered trial, `exact_msolve_full_prime2_pivot_order.*`,
completed a degree-four matrix of 45,045 rows by 2,656,383 columns and imported
1,985,794 new monomials. It then failed while growing the basis hash after
the next degree-four matrix (44,435 rows by 2,663,283 columns). Its solver
used 66.809504 CPU / 91.955289 wall seconds, exited with signal 11, and left
an empty basis file. The 2 GiB cap was unchanged. The input hash matches the
independent audit exactly. This progressed further but still supplies no
unrestricted count.

The alternative `--prime 2 --ternary-reduced all` exports the four-variable
elimination explicitly. It has 96 free ordinary cubic domains, 72 nonzero
reduced moments and four substituted pivot domains, hence 172 generators.
The `representatives` variant keeps 36 moments and has 136 generators.
Both have the full labeled count as their quotient dimension, with divisor
one. The [fresh geometric audit](exact_parity_math_reduced_input_audit.json)
independently derives the four linear substitutions and checks every emitted
polynomial, including every eliminated-cell cubic. It also checks the actual
adapter path. Neither dropping pivot domains nor treating free variables as
Boolean would preserve this count.

The reduced source JSON is pinned by SHA256, retained separately from the
hash of the emitted solver input. All model-option conflicts are rejected;
in particular the reduced characteristic-two export cannot be relabeled as
an odd-characteristic system or combined with a fixed prefix.

## Reserving only missing monomials

The support-only helper still reserved space for every referenced column,
even if its monomial already existed in the persistent basis hash. A third
[preserved build](exact_msolve_missing_promotion_tools/README.md) first checks
which referenced monomials are absent and reserves space only for those.
Existing entry IDs survive hash growth; absent entries are inserted in the
same ascending column order as before. This changes allocation, not the
retained polynomials, their coefficients or the critical-pair set.

The [independent review](exact_msolve_missing_review_notes.md) compared 25
completed bases with both the preceding binary and Python Buchberger. It
also checked 5,000 randomized mapping/capacity cases and 18 failure cases
under sanitizers. A separate 2,000-case harness used the actual upstream
lookup and rehash routines, including forced collisions and real growth.
The owner's 16 leading/full-basis comparisons were byte-identical, and the
known six-completion fiber remained six.

The third executable SHA256 is
`1e2111b5e1ef28201f3b2da6bc727d4563569e96b3468ab241433e7d2238a202`.
The old executables and all earlier run artifacts remain preserved.

The full ordered retry, `exact_msolve_full_prime2_pivot_missing.*`, used the
same input bytes and 2 GiB cap as the earlier ordered trial. It still failed
after 66.415649 CPU / 87.811644 wall seconds, without a basis or count. The
new diagnostic makes the second degree-four allocation precise: the basis
held 2,078,104 entries, and 55,218 new entries were needed. Their total,
2,133,322, exceeds the existing 2,097,152-entry array, so the upstream doubling
rule attempted 4,194,304 entries. That growth failed. Counting only missing
entries removes unnecessary reservations, but does not avoid this particular
capacity boundary.

The explicit reduced trial, `exact_msolve_full_prime2_reduced_all_missing.*`,
used the independently audited 96-variable, 172-generator input. Its first
degree-four matrix has 20,023 rows and 2,611,156 columns, fewer transient
rows than the unreduced model. The next round reaches essentially the same
capacity boundary: 2,080,795 existing entries plus 55,218 missing entries.
The attempted doubling again fails. Solver time was 69.012211 CPU /
99.694890 wall seconds; no completed basis or count was produced. The
actual input SHA256 is
`95363a4db10206ecc89852d09d93ac08d98311ea317af80c77f4488b72a3b66f`,
identical to the independently audited export.

## Reproduction

After the documented local setup and patched build, use a **fresh** output
prefix (existing artifacts are deliberately not overwritten):

```sh
python3 experiments/exact_algebra_backend_guarded.py --backend msolve \
  --output experiments/exact_msolve_full_prime2_reduced_fresh \
  --outer-seconds 240 --outer-memory-mb 2048 -- \
  --prime 2 --ternary-reduced all --seconds 180 --memory-mb 2048 --max-pairs 16 \
  --executable experiments/exact_msolve_missing_promotion_tools/msolve \
  --library-dir experiments/exact_algebra_backend_root/usr/lib \
  --require-export-marker
```

`-m` changes the batch size of critical pairs per matrix, not the complete
set of pairs that must be processed. A resource limit never establishes a
zero count. All ten cap fibers in the separate symmetry manifest also remain
uncounted.
