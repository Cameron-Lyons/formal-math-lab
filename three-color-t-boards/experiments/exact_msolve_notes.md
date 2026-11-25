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

The first unrestricted input is the ordinary F29 ring with 100 variables, all 100
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
cap. A later [selector audit](exact_msolve_pair_batch_analysis.md) identified
an offset in the pinned version's LCM boundary loop: it can exceed the
target or split a tie group, so complete tie preservation is not claimed.
The selected prefix is processed and removed; the unselected suffix remains.

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

## Separating exponent capacity from bucket capacity

A fourth [preserved build](exact_msolve_rounded_promotion_tools/README.md)
changes only the guarded promotion reserve. It rounds the required exponent
array capacity, including one spare slot, to a multiple of 65,536. Hash
buckets still have a power-of-two capacity at least twice the exponent
capacity. Existing IDs and insertion order are preserved. The preceding
failure would require 2,162,688 exponent slots rather than 4,194,304; for
96 variables, the principal basis-hash arrays fall from 904 MiB to
481.625 MiB. This is an allocation calculation, not a guarantee that every
later matrix will fit.

The [independent review](exact_msolve_rounded_review_notes.md) checked 25
completed bases with a deliberately tiny initial hash so the changed growth
path executes, plus real reallocation/collision cases, all four allocation
failure stages and boundary/overflow rejection. A separately attributed
compatibility harness exercised actual legacy growth, copy, clean,
reinitialization, secondary tables and reset after a non-power-of-two
exponent capacity. The owner also obtained 16 byte-identical leading/full
basis comparisons. All checks passed. New allocation failures exit with a
diagnostic; legacy growth behavior remains unchanged outside this helper.

The fourth executable SHA256 is
`cebd842aa617f09725a1f5429ebc822da238563f142b14993cccb85312d1874c`.

The full reduced retry, `exact_msolve_full_prime2_reduced_all_rounded.*`,
successfully crosses the old capacity boundary and completes the second
degree-four round. The next matrix has 26,569 rows and 2,626,958 columns.
Its linear algebra crashes before completing the round, after 89.876150 CPU /
91.511242 wall seconds. The basis file remains empty and no count exists.

Two bounded debugger reproductions preserve the same input, executable and
2 GiB limit. The second captures `R12=0`, `RSI=0` and fault address `0x18`
at the first output-row write. Disassembly maps `R12` directly to the
unchecked `malloc` return at `src/neogb/la_ff_8.c:542`; the failing write is
line 548. This confirms a null output-row allocation, not merely a guess
from the signal. Its requested byte count was not captured. The
[source/disassembly report](exact_msolve_la_analysis.md) records the mapping.
Diagnostic artifacts have status `DEBUG_ONLY_NO_COUNT`, even though batch
gdb exits successfully after reporting the inferior's crash. They are never
accepted as counting results. Both diagnostic runs terminated; no inferior
was left running.

## Smaller batches and live progress

The same audited reduced input and fourth executable were run with pair
batch target one in `exact_msolve_full_prime2_reduced_pairs1.*`. This trial
completed 24 matrix rounds without the earlier crash, but reached its
180-second solver wall limit while still processing degree-four pairs.
The last completed round had 12,119 rows and 2,552,995 columns; the next
pending-pair count shown is 293. Solver time was 168.970484 CPU /
180.147790 wall seconds. Status is `INCOMPLETE_TIMEOUT`, the basis file is
empty and no count exists. The target reduces working memory at a time cost;
these results do not establish that a longer run will finish.

The adapter now streams stdout/stderr directly into a fresh, exclusively
created `.log` during execution. Completed logs are not rewritten. The
existing completion, timeout, error, unique-marker and strict-basis gates
remain unchanged. The adapter review checks live visibility, retained
timeout output and overwrite rejection; a real small fixture returns six.
Live diagnostic output is not a completed-basis attestation.

A proposed 300-second trial with a 3 GiB address-space cap did **not start**.
Although available memory initially measured about 4 GiB with no solver
running, it fell below the explicit 3.5 GiB preflight threshold before
launch (a subsequent check showed 2,788 MiB available). No artifacts or
results are attributed to that unstarted trial. All full trials described
above used a 2 GiB cap and are terminal.

## Complete cap split and later ordered F29 trial

The ten top-two-row cap orbits form a complete partition of all 81 caps.
Their raw fixed-prefix completion counts must be combined with their actual
orbit weights, which sum to 81; the weights are not uniformly 12. The
[independent cap audit](exact_msolve_cap_split_notes.md) checks all ten models
in characteristics 2 and 29 and supplies a strict msolve aggregation adapter.
Cap `0000` has 96 variables, 176 generators and quotient divisor one. The
other nine caps require a coefficient-extension variable and divisor two.
No complete cap count is currently available, so no aggregate is available.

The first cap trial, `exact_msolve_cap0000_prime2.*`, used the fourth rounded
build, pivot order, pair target 16 and a 180-second/2 GiB solver limit. The
actual input was independently checked against fresh geometry. It completed
12 rounds; the last completed degree-four matrix was 34,368 by 2,575,926.
The next log header shows degree 4 and 903 pending pairs, with no matrix
dimensions printed. The solver reached its wall limit after 158.440272 CPU /
180.242095 wall seconds. This is `INCOMPLETE_TIMEOUT`, with an empty basis
and no count. This fixed four-cell fiber must not be confused with the
previously completed nine-row six-completion fiber.

The full ordered F29 trial, `exact_msolve_full_prime29_pivot_rounded.*`, used
the fourth build, 100 variables/180 generators, divisor one, pair target 16,
and a 120-second/2 GiB solver limit. It completed five rounds, ending with a
degree-three matrix of 18,741 by 169,762. The next degree-four selection
header shows 341 pending pairs, but no matrix dimensions or specific failure
diagnostic. The solver exited with signal 11 after 90.237675 CPU / 91.784131
wall seconds. Its status is `BACKEND_ERROR`, not a timeout. These artifacts
do not establish the fault location or allocation that caused the signal.
No basis or count was produced.

The input hashes are respectively
`4aa5a5354dd1596d4240992c8a078604beecee72808a2b66f9106aafea602900`
and `699e6a81b2f4c1b113a448dc17e5b81f5962a365729204ae32802c857fd9944d`.

## Serial F2 matrix kernel

A fifth [preserved build](exact_msolve_f2_bitset_tools/README.md) uses exact
bitset Gaussian elimination for the guarded serial characteristic-two
ordinary basis-export path. It keeps the existing kernels for other modes.
This changes matrix coefficient storage and reduction, not the polynomial
ring: the variables still have ordinary cubic domains. Old sparse reducer
rows are freed before new sparse output is materialized. Checked allocation
failures terminate without a completed-basis attestation.

The corrected fifth executable SHA256 is
`78e65a3c746a036d12ac67d8c332a9afd2101746eee3b850d4a2ecb5e696f502`.
An initial draft rejected the upstream converter's unsorted sparse tails;
it failed closed and is preserved separately. The corrected version allows
tail permutations while checking uniqueness and the leading-column rule.
The [independent review](exact_msolve_f2_review_notes.md) checked 1,039 actual
kernel matrices under address/undefined-behavior sanitizers, 19 allocation
failure cases, 16 invalid-input/mode cases and 12 complete F2 polynomial
ideals against Python Buchberger and the preceding build. The owner also
checked integrated exports and fallback modes; the report attributes these
separately.

The full trial `exact_msolve_full_prime2_bitset.*` used the same independently
audited 96-variable/172-generator reduced input as the earlier rounded run,
pair target 16 and a 180-second/2 GiB limit. It completed the previously
failing degree-four matrix of 26,569 by 2,626,958. That round produced 17 new
polynomials and 16,626,336 sparse output terms; these are matrix diagnostics,
not board counts. The next matrix was 19,153 by 2,615,528, and its log ends
with `MSOLVE_F2_BITSET_ERROR: allocation failed`. The solver exited normally
with failure code 1 after 133.624000 CPU / 145.619429 wall seconds; it did not
terminate by a signal or hit the wall limit. Status is `BACKEND_ERROR`.
The input remains
`95363a4db10206ecc89852d09d93ac08d98311ea317af80c77f4488b72a3b66f`.
No completed basis or count exists.

## Redundant exact histogram constraints

The `--histogram-e2` option appends four role elementary-symmetric quadratic
constraints and their four Frobenius partners to an unrestricted F2 model.
All base domains and Fourier polynomials remain. The
[independent proof/input audit](exact_elementary_review_notes.md) verifies
the role-difference identities modulo existing unary equations, retained
ordinary squares and partner linear terms, and the ideal-equality argument
using radicality of the complete cubic-domain quotient. This augmentation
does not change the quotient dimension or divisor. It is not a replacement
for the Fourier constraints and cannot be combined with a fixed prefix.

The full trial `exact_msolve_full_prime2_elementary.*` used the corrected
fifth build, the augmented reduced model with 96 variables/180 generators,
pair target 16 and a 180-second/2 GiB limit. Four rounds completed through
degree 3; the last was 913 by 151,212. The next selection header shows
degree 4 and 345 pending pairs, with no matrix dimensions or specific failure
diagnostic. The solver exited with signal 11 after 121.120406 CPU / 134.879057
wall seconds. Status is `BACKEND_ERROR`, not a timeout. The log does not
identify the fault location or prove a particular allocation failure.
The independently audited augmented input hash is
`4338b3f86b8738130edbfb788504de14be08c60ada263afeba3f9844b437dd90`.
The base hash remains separately recorded in metadata. No completed basis
or count exists.

These four trials have an empty `.basis`, no `.leading.json`, no export
completion marker and no quotient/board count. Their outer wrappers report
`OUTER_PROCESS_FINISHED` with return code 1 and no outer wall timeout. That
status means the wrapper process finished; it does not mean the solver
succeeded. Times above are the solver child user+system CPU and elapsed wall
times, not the outer process-tree totals. The
[consolidated audit](exact_msolve_current_trials_audit.json) preserves the
earlier entries and records exact statuses, scopes, hashes and log evidence.
`exact_msolve_terminal_audit.py` reproduces this read-only artifact audit.

## Invertible prefix coordinates

The next model changes coordinates by prefix sums along a recorded
permutation of all 100 original cells, then eliminates four unary linear
equations. The [independent source and adapter audit](exact_pivot_review_prefix_notes.md)
checks the forward/inverse linear maps, all 100 transformed original cubic
domains, 72 nonzero Fourier moments, eight elementary equations, and the
optional 96 quartic field equations. The resulting quotient is isomorphic
to the original full counting quotient, with divisor one. Free prefix
coordinates can be zero; no blanket cubic domains are imposed on them.
Ordinary fourth powers remain fourth powers.

The actual transformed nine-row validation completed with quotient dimension
12 and coefficient-extension divisor two, giving six fixed-prefix boards.
An independent read/recount checked all 358 input polynomials and both integer
counters. The original outer process stopped at a postprocessing variable-name
exception after the solver completed. The raw completed export was recovered
by verifying its actual `x1,...,x96,a` header and applying only the identifier
alias `a` to `x97`; the solver was not rerun. The original exception and
metadata corrections are preserved. Only rounded solver-reported times
(3.14 CPU / 3.17 wall seconds) survived; exact subprocess timings are
unavailable. This completed fiber supplies no unrestricted count.

The unrestricted trial `exact_msolve_full_prime2_prefix_gray_3g.*` used the
corrected fifth executable with all moments, e2 constraints and optional
quartics: 96 variables and 276 generators. It used pair target 16, a
300-second solver / 360-second outer wall limit, and a 3 GiB address-space
limit. The actual input matches the independently audited input hash
`60a5280098df62e0607fd3762a6e501b2d6098609b772138bd08f4f7ef867311`.

It completed 29 rounds with reported timings, including four degree-five
rounds. The last fully completed round had 42,033 rows and 753,562 columns.
The next degree-five matrix had 210,803 rows and 6,546,994 columns; linear
algebra returned nine rows with 5,528,411 output terms. Promotion then needed
3,463,587 missing monomials in addition to 1,462,002 existing entries. The
guarded allocator requested 4,980,736 exponent slots, up from 1,572,864, and
16,777,216 hash buckets. It explicitly reported
`Error: cannot allocate promotion exponent data.` before importing the
new rows into the basis.

The solver exited with failure code 1 after 248.070159 CPU / 252.145026 wall
seconds. The outer process finished after 252.462974 wall seconds without
reaching its time limit. Status is `BACKEND_ERROR`, not a timeout. The basis
file is empty, no leading export or completion marker exists, and no quotient
or board count exists. Reaching degree five is a diagnostic observation,
not a completed exact computation. These terminal facts and artifact hashes
are included in `exact_msolve_current_trials_audit.json`; no resource-limit
failure is treated as a zero count.

The subsequent `--histogram-e4` augmentation adds four ordinary quartics
with 12,324/1,146/278/446 terms. The
[independent e4 audit](exact_pivot_review_e4_notes.md) verifies their exact
role-difference certificates using the retained unary equations, e2
conditions and transformed original cubic domains. It also checks every
appended polynomial through all four allowed backend preparation modes.
The flag requires prefix coordinates and e2; it retains all base equations
and changes neither the quotient nor its divisor.

The comparison run `exact_msolve_full_prime2_prefix_gray_e4_3g.*` used the
same executable, pair target 16, 3 GiB cap and 300/360-second solver/outer
limits. Only these four equations were added, giving 96 variables and 280
generators. Its input hash is
`72b09d3e2df822ea72f09dd1876580e950642a5681177d7aa604e8f6a68d9081`,
and metadata separately retains the preceding input hash. The run completed
30 rounds with reported timings. Its last completed degree-five matrix was
43,637 by 891,323. The next selection header shows degree 5, 17 selected pairs
and 3,246 pending pairs, without matrix dimensions. The solver then reported
`Enlarging exponent vector for hash table failed` and
`for esz = 8388608, segmentation fault will follow.` The log identifies a
failed exponent-vector enlargement but does not itself identify which hash
table was being enlarged.

The solver exited with signal 11 after 199.883521 CPU / 203.774695 wall seconds.
Its terminal status is `BACKEND_ERROR`. The outer wrapper finished after
204.275440 wall seconds without a timeout. The basis is empty, no leading
export or completion marker exists, and neither a quotient nor a board count
was computed. This second 3 GiB trial is also recorded in the consolidated
terminal audit, preserving all earlier records.

## Natural characteristic three and staged symbolic storage

The exact model can instead use the actual palette `0,1,2` in F3. Its
invertible three-color power transform forces all 81 pattern counts to be
one modulo three; nonnegativity and the total of 81 then force each count
to be exactly one. A signed prefix coordinate change and four independent
unary eliminations leave 96 free variables. Unlike the nonzero-root F4
encoding, the transformed field-domain ideal is generated by the 96 simple
equations `x_i^3-x_i`. The independent
[F3 source and proof review](exact_f3_review_notes.md) checks all 76 remaining
power moments, the four additional redundant histogram cubics, and the
actual backend preparation. Both base and augmented quotient dimensions
equal the full labeled board count, with divisor and multiplier one.

The separately preserved sixth msolve build stages only genuinely missing
symbolic exponent vectors before growing the retained basis table. It
releases the old symbolic table's private arrays and restores a small valid
secondary table while preserving borrowed data and insertion order. Build
6b extends that guarded path to F3. Its
[independent review](exact_msolve_staged_review_notes.md) includes 1,200
sanitizer cases, allocation failures, complete bases against an independent
Python implementation, and a byte-level check of the one-line F3 gate
extension. This storage change does not modify the polynomial ideal.

The full run `exact_msolve_full_native3_e3_staged_3g.*` used build 6b
`9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a`,
pair target 16, exact sparse linear algebra, a 3 GiB address-space cap, and
300/360-second solver/outer limits. Its 96-variable, 176-generator input
hash is `cb2497554585e51166b747cee0221efc3cf7f130f46b9084d7f2e9d3b760c105`.
It completed 23 rounds with printed timings and exercised seven symbolic
staging operations. No F2 bitset kernel was used in this F3 run.

The last completed degree-five matrix had 21,640 rows and 1,032,184 columns,
producing 13 new rows. The subsequent promotion successfully staged 837,014
missing monomials in 162,380,910 exponent bytes and grew the retained basis
capacity to 1,769,472. The next degree-five selection shows 16 pairs and
2,776 pending pairs, but no matrix dimensions. The log then explicitly
reports `Enlarging exponent vector for hash table failed` and
`for esz = 8388608, segmentation fault will follow.` The log identifies the
failed allocation class and requested capacity, but does not itself name
the particular hash table.

The solver terminated with signal 11 after 198.575927 CPU / 202.796805 wall
seconds. The outer wrapper finished after 203.698359 wall seconds without
a timeout. Status is `BACKEND_ERROR`: the basis file is empty, the leading
export is absent, completion markers number zero, and no quotient or board
count exists. The independent read-only terminal audit is
`exact_f3_terminal_review_results.json`; the consolidated trial audit
preserves all earlier entries. Successful staging and reaching degree five
do not establish a completed count.

The next run made the global translation factor explicit while retaining
the apex-color field domain inside the input. Thus its quotient dimension
would still be the full count, with divisor and multiplier one. Its 96
variables consist of 95 coupled normalized coordinates and one independent
F3 apex-color coordinate. The separately verified variable transformation,
optional e3 equations and known six-completion fiber are documented in the
[F3 review](exact_f3_review_notes.md).

`exact_msolve_full_native3_translation_e3_symbolic_3g.*` used translated
input `44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5`
and the seventh executable
`a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a`.
That build reserves symbolic row capacity through the checked allocator;
its source and independent tests are recorded in
[the symbolic-reservation review](exact_msolve_symbolic_review_notes.md).
The trial retained the 3 GiB cap, pair target 16 and 300/360-second
solver/outer limits. The saved preflight recorded 4,424 MiB available
against the required 3,584 MiB.

This trial reached its child wall-time limit, with terminal status
`INCOMPLETE_TIMEOUT` after 247.204902 CPU / 300.256586 wall seconds. The
outer wrapper finished after 301.456276 wall seconds without reaching its
own limit. No solver return code is recorded for the child timeout, and
no raw allocation-failure or other error diagnostic appears in its log.
It completed 25 rounds with reported timings. The last completed
degree-five matrix had 29,856 rows and 1,395,306 columns; the next selection
shows 16 pairs and 3,120 pending pairs without matrix dimensions.

The log records 121 symbolic row reservations and seven staging operations.
Its last symbolic request was for 3,604,480 exponent entries, rounded from
the checked bound of 3,578,597 entries including the spare. These are
reservation bounds, not measured matrix-column counts or a memory-fit
guarantee. The basis file remains empty, no leading export or completion
marker exists, and no quotient or board count was computed. The independent
terminal report is `exact_f3_translation_terminal_review_results.json`,
and the consolidated audit preserves all previous trial records.

## Minimum-fill native-F3 trials at 3 and 4 GiB

The seventh executable `a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a`
ran the same minimum-fill input `b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`
in two sequential trials. This remains the unrestricted 96-variable,
176-generator F3 ideal: the independent apex-offset field variable is retained,
so its quotient dimension would already equal the full labeled count (divisor
and multiplier one). Both had a 900-second child and 960-second outer limit.

The 3-GiB trial was `BACKEND_ERROR`, exit 1, after 285.469678 CPU seconds and
328.585865 child wall seconds. Its last completed degree-five matrix had
17,439 rows and 3,200,323 columns. The next round's checked symbolic reserve
requested 5,505,024 exponent slots after a confirmed capacity of 5,177,344,
and allocation failed.

The 4-GiB retry changed only the memory limit. Its preflight recorded 4,824 MiB
available against the required 4,608 MiB. It was `BACKEND_ERROR`, exit 1,
after 331.312459 CPU seconds and 351.842617 child wall seconds; outer elapsed
time was 353.476518 seconds and process-tree CPU time 333.052073 seconds.
It completed 22 timed rounds, last a degree-five 32,889 by 3,894,880 matrix.
The next round requested 7,733,248 symbolic exponent slots from 7,536,640:
5,097,099 existing entries plus a 2,608,997-term row and one spare required
7,706,097 slots. Its 16,777,216-bucket table did not need growth. The checked
exponent-data allocation failed. The allocator's generic error text says
“promotion exponent data”; the immediately preceding capacity diagnostic
identifies this as a symbolic-table request.

The independent terminal audits check actual input, executable and preflight
hashes, inverse variable maps and count scope, result/outer terminal statuses,
raw logs, empty basis files, zero completion markers and absent leading-ideal
exports/count fields. Neither trial supplies a count, zero proof, or partial
count. Reports are `exact_f3_order_terminal_review_results.json` (3 GiB) and
`exact_f3_order_terminal_review_4g_results.json`; both are preserved in
`exact_msolve_current_trials_audit.json`. The audits start no solver.

## Checked-byte exponent build review

The separately preserved eighth build stores ordinary F3 exponent lanes in
one checked byte. Its scope requires explicit field domains for every
variable, field-reduced remaining input terms, at most 127 variables and
serial exact DRL export. It does not reduce ordinary exponents modulo 256.
The [independent review](exact_msolve_byte_review_notes.md) passed for executable
`63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`:
20 Python-reference/exhaustively enumerated ideals, 80 complete native exports,
34 fail-closed input/mode cases and an independent sanitizer arithmetic harness.
The actual unrestricted minimum-fill input passes source-only guard checks.
No full solve was performed by that review, and this storage change supplies
no new count by itself. Earlier builds and failed trial artifacts are retained.

## Remaining color-reversal symmetry

The native-F3 adapter supports two separately audited alternatives, both
requiring `--prime 3 --ternary-native-field --native-e3 --native-translation`:

- `--native-sign` adds the quintic selector and retains independent offset
  and sign variables. Its 97-variable, 179-generator quotient still counts
  every labeled board directly.
- `--native-sign-branch K`, for K=0,1,2,3, adds sparse linear constraints
  instead of the quintic. Each quotient counts only its specified branch,
  with both finite factors included. All four branch dimensions are needed.

Either supports the independently checked `--native-order minimum-fill`
permutation. The two alternatives are mutually exclusive. Both export
bilinear original-color reconstruction, `z=a+s*d`; original-color fixes
must use this formula. There is no external multiplier of two, three or six.

For a linear branch, `--native-branch-elimination` substitutes out its solved
canonical coordinates. The resulting models have 96, 95, 94 or 93 variables,
depending on the branch. Canonical colors now have affine reconstruction;
the actual-color formula still includes both `a` and `s` and can have linear
`s` terms. The helper therefore supplies affine canonical forms and explicit
degree-at-most-two actual-color polynomials. Eliminated and uneliminated
inputs count the same branch; they are not separate summands.

The [sign-model review](exact_algorithms_sign_review.md) checks both complete
inputs and reproduces the known six-solution prefix. The
[branch-adapter review](exact_algorithms_branch_adapter_review.md) checks all
eight inputs and reproduces the fixed-prefix dimensions `6,0,0,0` with both
integer counters agreeing. These are validation results, not full counts.
The [strict branch aggregator](exact_sign_branch_aggregate.md) requires one
complete, verified result for each branch and rejects fixed-prefix inputs,
duplicate orders, incomplete results and any attempt to treat missing work
as zero.

Review found that a prepared `standard_basis_complete=False` metadata field
was not updated by the shared runner after successful basis parsing. The
runner now sets both completion flags together. The five affected small
fixture records retain verbatim `*.pre_flag_fix.json` originals and explicit
metadata-only correction audits; input, output, counts and execution details
are unchanged. A full run started before this correction retains its actual
original metadata and must be audited against the completed export itself.

## Eighth-build full minimum-fill trial: terminal segmentation fault

The checked-byte executable `63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`
ran the unchanged unrestricted minimum-fill input `b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`
with a 4-GiB address-space cap, 900-second child limit and 960-second outer limit.
The preflight recorded 4,942 MiB available, exceeding the required 4,608 MiB.
It terminated before either time limit: `BACKEND_ERROR`, solver return code
-11 (SIGSEGV), wrapper exit 1. Child time was 546.706832 CPU seconds and
564.328089 wall seconds; outer time was 565.571819 seconds with 548.501306
process-tree CPU seconds.

The final log records 24 completed timed rounds. After the seventh build's
last completed 32,889 by 3,894,880 matrix, this build completed degree-five
matrices of 57,321 by 5,384,334 (15 new rows) and 21,124 by 6,530,168 (16 new
rows). The latter promotion inserted 2,101,181 monomials and confirmed a
retained-basis capacity of 7,929,856. Its next degree-five batch selected 16
pairs with 2,690 pending and did not print matrix dimensions.

The last logged symbolic reserve requested 10,878,976 exponent slots from
9,830,400, with 33,554,432 buckets unchanged. Its required load was
6,439,449 existing entries plus a 4,424,268-term row and one spare, totaling
10,863,718. There is **no explicit allocation or arithmetic failure diagnostic**
in the raw solver log. That last request does not establish where or why the
segmentation fault occurred; an allocation cause remains unconfirmed.

The strict terminal audit verifies the actual input and variable maps, the
frozen executable and preflight, normal outer termination, an empty basis,
zero export-completion markers, absent leading export and absent count fields.
The 96-variable, 176-generator input still retains the independent translation
field factor, with divisor and multiplier one, but supplies no quotient
dimension or board count. The original terminal JSON is preserved, including
its preparation-era false completion flag. Report:
`exact_f3_byte_terminal_review_results.json`; the same record is appended to
`exact_msolve_current_trials_audit.json`. No solver was started by the audit.

## Eighth-build full quintic-sign trial: terminal segmentation fault

The next full input added the reviewed quintic sign selector and retained both
independent finite factors: the offset variable over F3 and the nonzero sign.
Its 97-variable, 179-generator quotient dimension would directly equal the
full labeled count, with divisor and multiplier one. The actual input hash is
`14247d0e4cfaff8636e99852902816d8d0ab97de47ada08cb2e40fa7576e71cf`;
the eighth executable remains `63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`.

The run used 4 GiB, a 900-second child limit and 960-second outer limit, after
preflight recorded 4,704 MiB available against 4,608 required. It terminated
with `BACKEND_ERROR`, solver return code -11 (SIGSEGV), wrapper exit 1, after
567.581942 child CPU seconds and 598.196531 child wall seconds. Outer elapsed
time was 598.320039 seconds; process-tree CPU time was 568.314047 seconds.

There were 24 completed timed rounds. The last degree-five matrix was
21,124 by 6,530,168, and its final promotion confirmed basis capacity
7,929,856. The next degree-five batch selected 16 pairs, with 2,691 pending,
and printed no matrix dimensions. The final symbolic request was again
10,878,976 exponent slots from 9,830,400, requiring 10,863,718 entries including
the spare, with 33,554,432 buckets unchanged. The raw log contains no explicit
allocation or arithmetic error. The capacity request and SIGSEGV do not by
themselves confirm the failure's cause.

`exact_f3_sign_terminal_review.py` verifies the actual source/model hashes,
97-variable reconstruction and both retained factors, exact command,
executable/libraries, preflight and outer completion. The actual basis is
empty, there are zero completion markers, and there is no leading export or
count field. The terminal record is `exact_f3_sign_terminal_review_results.json`
and is preserved in `exact_msolve_current_trials_audit.json`. No full count or
zero result is inferred. The audit started no solver.

The audit's optional stdout redirection to `/tmp` encountered a quota error
after its repository JSON reports had been completely written. Both reports
were re-read and parsed successfully; the original solver artifacts are
unchanged. This separate audit-output issue is not evidence about the earlier
solver SIGSEGV. Subsequent audit scratch files use the workspace filesystem.

## Affine-eliminated branch 3 at 3 GiB: terminal segmentation fault

The first unrestricted branch-3 trial used the reviewed affine elimination,
minimum-fill input `f752d055d104dc6cd2d2599ce52c5931f1f6f8e082703eac42c978bfbbb033ae`,
with 93 variables and 174 generators, on eighth executable `63e52125...`.
This is the full labeled fiber of branch 3, not the whole four-branch union.
Offset and sign remain at zero-based indices 91 and 92; no multiplier or
divisor is applied. Its dimension is presently unknown.

An initial 4-GiB preflight was deferred without a solver. The actual launch
used 3 GiB after recording 4,499 MiB available against 3,584 required, with
900-second child and 960-second outer limits. It terminated before either
limit: `BACKEND_ERROR`, solver return code -11 (SIGSEGV), wrapper exit 1.
Child CPU and wall times were 423.038078 and 452.188978 seconds; outer elapsed
time was 452.341549 seconds and process-tree CPU time 423.616 seconds.

The log records 18 completed timed rounds. The last degree-five matrix was
36,782 by 4,085,322; the final promotion inserted 1,519,984 monomials and
confirmed a basis capacity of 4,587,520. The next batch selected 16 pairs with
1,983 pending and printed no matrix dimensions. Its final symbolic request
was 6,946,816 exponent slots from 6,488,064, requiring 6,881,670 entries
including the spare; the 16,777,216 buckets were unchanged. The raw log
contains no explicit allocation or arithmetic failure diagnostic, so the
underlying SIGSEGV cause is unconfirmed.

The new single-branch terminal mode independently verifies the exact frozen
scope and reconstruction, executable/libraries and command, actual 3-GiB
preflight, and completed outer process. The basis is empty, zero completion
markers are present, and there is no leading export or count field. Both
branch count and full total remain **null, not zero**. Report:
`exact_f3_branch3_terminal_review_3g_results.json`, also appended to
`exact_msolve_current_trials_audit.json`. Full-count lower-bound/divisibility
checks are not applied to one branch; they apply only to the certified sum
of all four. No solver was run by this audit.

## Reset-option source finding

The [reset-option review](exact_msolve_reset_review.md) finds that the frozen
eighth build's ordinary F3 export path never calls `reset_hash_table`.
`-u1`/`-u5` are parsed and displayed but cannot reclaim ordinary table IDs.
The sole source invocation is inside a saturation/tracing routine excluded by
the byte build's guards. Eighteen tiny g1/g2 comparisons, including the known
six-completion prefix, give identical bases and allocation/promotion sequences
for `-u0`, `-u1` and `-u5`. No full reset-option run or backend change was made.
If the helper were called, it would retain capacity and temporarily allocate
a second same-size exponent slab and pointer array; memory savings cannot be
inferred merely from its name or an enabled printed interval.

## Affine-eliminated branch 3 at 4 GiB: terminal child timeout

The fresh `exact_msolve_branch3_eliminated_minfill_byte_4g_waited.*` trial used
the same branch-3 minimum-fill input `f752d055d104dc6cd2d2599ce52c5931f1f6f8e082703eac42c978bfbbb033ae`
and eighth executable `63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`.
The 93-variable, 174-generator scope remains full labeled boards in branch 3,
with offset/sign factors retained and divisor/multiplier one. Earlier deferred
4-GiB preflights remain separate artifacts and did not start solvers.

After bounded availability checks of 4,492, 4,546 and 5,138 MiB, this actual
launch passed the 4,608-MiB requirement for a 4-GiB cap. The child reached its
900-second wall limit, reporting `INCOMPLETE_TIMEOUT`, rather than a completed
basis. Recorded child time was 576.156232 CPU seconds and 900.292436 wall
seconds. The wrapper then finished with exit 1 after 900.434608 seconds,
with 576.993553 process-tree CPU seconds; its separate 960-second outer limit
was not reached. A normal solver return code is absent for the child timeout.

The log records 19 completed timed rounds, including one further degree-five
matrix beyond the 3-GiB trial: 42,571 by 5,264,659. Its promotion inserted
1,102,046 monomials and confirmed a retained-basis capacity of 5,701,632.
The next degree-five batch selected 16 pairs with 2,197 pending and printed
no matrix dimensions. The final symbolic request was 8,912,896 exponent slots
from 8,847,360, requiring 8,863,235 entries including the spare
(5,510,079 existing plus a 3,353,155-term row plus one). The 33,554,432 buckets
were unchanged. There is no raw allocation or arithmetic error diagnostic;
the final capacity request is not evidence of an allocation failure.

The generic single-branch terminal audit verifies the frozen actual input,
variable reconstruction, executable/libraries and exact command, actual
4-GiB preflight and completed wrapper. It confirms an empty basis, zero
export markers, no leading export and no count fields. **Branch 3 remains
unknown, not zero, and the full four-branch total remains unknown.** Report:
`exact_f3_branch3_terminal_review_4g_results.json`; the record is also in
`exact_msolve_current_trials_audit.json`. No solver was started by this audit.

## Reproduction

After the documented local setup and patched build, use a **fresh** output
prefix (existing artifacts are deliberately not overwritten):

```sh
python3 experiments/exact_algebra_backend_guarded.py --backend msolve \
  --output experiments/exact_msolve_full_prime2_reduced_fresh \
  --outer-seconds 240 --outer-memory-mb 2048 -- \
  --prime 2 --ternary-reduced all --seconds 180 --memory-mb 2048 --max-pairs 16 \
  --executable experiments/exact_msolve_rounded_promotion_tools/msolve \
  --library-dir experiments/exact_algebra_backend_root/usr/lib \
  --require-export-marker
```

`-m` changes the batch size of critical pairs per matrix, not the complete
set of pairs that must be processed. A resource limit never establishes a
zero count. All ten cap fibers in the separate symmetry manifest also remain
uncounted.
