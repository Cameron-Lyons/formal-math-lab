# Investigation of the exact ternary count

For the number *N* of valid labeled three-color T boards, the tightest verified bounds are

**45,083,592 ≤ N ≤ 1,185,818,059,470,602,086,065,654,202,368.**

[Lower-bound certificate](SplicePalCertificates.lean) · [Four-row upper-bound census](experiments/exact_rotor_upper_results.json) · [Independent upper-bound audit](experiments/exact_rotor_upper_review_results.json)

## A global symmetry theorem

Every valid ternary board has exactly **12 distinct images** under the six
color permutations and horizontal reflection. This holds for every valid
board, including boards absent from all existing certificates.

Validity makes the map from the 81 placements to the 81 ordered patterns a
bijection. If a recolored reflection fixed a board, this bijection would
identify fixed placements with fixed patterns. Reflection has nine fixed
placements. Depending on the color permutation, the corresponding action
on patterns has 27, 3, or 0 fixed patterns, never nine. For an unreflected
color permutation, all 81 placements are fixed, and only the identity
permutation fixes all 81 patterns. Thus the identity is the only stabilizer.
The orbit size 12 follows by composing and inverting these actions.

[ExactSymmetry.lean](ExactSymmetry.lean) kernel-checks the unrestricted
stabilizer theorem, `TBoards.ExactSymmetry.stabilizer_trivial`. Its hypothesis
is `Valid b`, with no assumptions about the board's cap, pivot, or provenance.
[ExactOrbit.lean](ExactOrbit.lean) kernel-checks the twelve-image corollary
from the same hypothesis alone. `TBoards.ExactOrbit.twelve_distinct_images`
states that the list `orbit b` of the twelve transforms of `b` has length 12,
has no repeated entry, and contains only valid boards.
The same file kernel-checks the counting step,
`TBoards.ExactOrbit.length_eq_twelve_mul_canonical`: a duplicate-free list of
valid boards that contains all twelve images of each of its boards is twelve
times as long as its sublist chosen by any selector that picks exactly one of
the twelve images of each board. A list of all valid boards is such a list.
That a given encoding's canonical-form clauses are such a selector, and that
its models are the valid boards, is not formalized.

```sh
lake build ExactSymmetry ExactOrbit
```

The build logs for the [stabilizer theorem](exact-symmetry-lean-build.log)
and the [twelve-image corollary and counting step](exact-orbit-lean-build.log)
record successful builds and only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.

A further [finite-rank argument](experiments/exact_structure_gauge.md) rules
out enlarging this reduction through fixed independent color permutations
at individual cells. If such a transformation preserves every valid board,
all 100 cell permutations must agree. Just 322 explicit valid test boards
force this conclusion, through 160 XOR identities and a rank-161 certificate.
The certificate has been independently checked; this additional argument is
not formalized in Lean.

The same investigation proves that cell relocations preserving the uncolored
T-incidence system are only identity and reflection. Together with fixed
cellwise recolorings, these give exactly the known twelve transformations.
The result does not exclude transformations chosen after inspecting a board,
or spatial permutations preserving solutions without preserving incidence.

An [exhaustive symmetry split](experiments/exact_parity_math_symmetry.md)
reduces the full count either to three times the apex-zero count or to a
weighted sum of ten top-two-row fibers. The cap orbit weights sum to 81;
they are not uniformly twelve. The
[manifest and strict aggregation audit](experiments/exact_symmetry_split_notes.md)
independently reproduce the binary total 168 and refuse to publish a ternary
total until every required fiber has a matching, audited complete count.
Global cubic homogeneity recovers the apex factor three and supplies no
additional reduction. The characteristic-29 apex-zero algebra trial also
exhausted its 2 GiB limit before producing a basis or count.

The [msolve cap auditor](experiments/exact_msolve_cap_split_notes.md) now
supports the same complete ten-case sum with explicit coefficient-extension
divisors and strict input/basis provenance. Its independent geometry audit
checks all ten models in both characteristics 2 and 29. The first four-cell
case, `0000`, timed out after 180 seconds without a basis; no required cap
count has yet been obtained.

## Exact algorithms and their measured limits

The [row-transfer census](experiments/exact_algo_frontier.cpp) merges prefixes
with the same last row and the same set of used patterns. With the apex
fixed to 0, there are exactly 9,391,598 distinct-pattern four-row prefixes,
but still 9,379,134 different transfer states. Merging removes only about
0.13% of prefixes at this depth. A straightforward table of these states
therefore does not yet offer the compression needed for a full count.

The [streaming counter](experiments/exact_algo_count.cpp) supports deterministic
prefix intervals. It distinguishes `COMPLETE` from `INCOMPLETE`, and discards
the partial count of an unfinished interval element. This makes its completed
interval results additive without treating a time limit as an exhaustive
result. The [cap census wrapper](experiments/exact_algo_census.py) groups
prefixes into explicitly enumerated symmetry orbits and counts extensions
with their actual orbit sizes. Partial caps can have stabilizers, so a
uniform multiplier of twelve would be incorrect for this intermediate step.

This census exhausted all 1,572 three-row prefix orbits and found exactly
**198,649,032,096 five-row caps** whose 16 T patterns are distinct. These are
25-cell partial boards; the count does not assert that they extend to valid
100-cell boards. The computation took about 189 seconds. Every prefix,
its orbit size, and its exact completion count are saved in
[the census results](experiments/exact_algo_census_results.json).
The [counter report](experiments/exact_algo_results.md) gives the exact
scope, symmetry accounting for partial caps, and independent validation.

```sh
python experiments/exact_algo_census.py --seconds 300
```

The [CNF model](experiments/exact_count_cnf.py) is count preserving: its cell
variables encode the board, and its auxiliary variables are uniquely
determined. Deterministic model counting reproduced the complete binary
count of **168**, as well as **two** completions for a published seven-row
ternary prefix. Full symmetry normalization selects exactly **42** binary
boards, and was checked on all 17,160 images of the earlier 1,430 ternary
representatives. With `--orbit-canonical`, the ternary model count must be
multiplied by twelve. A six-row ternary prefix trial did not finish within 60
seconds; an unrestricted ternary trial with color normalization did not
finish within 120 seconds, and a trial using full symmetry normalization
did not finish within 60 seconds. These time limits yield no exact count for
either unfinished problem. [Encoding, commands, and solver provenance](experiments/exact_count_notes.md)

Independent enumeration by
[local output permutations](experiments/exact_math_rotors.py) also reproduced
all 168 binary boards, comparing the complete board set with the earlier
cell-by-cell enumerator. Every valid ternary board is uniquely specified by
19 boundary colors and 27 permutations of the three possible output colors,
subject to a deterministic acceptance test. This gives a rigorous upper
bound of

```text
3^19 × 6^27 = 1,189,563,417,824,350,846,613,100,429,312.
```

It is not an exact count: many parameter tuples fail the acceptance test.
It does ensure that the new streaming counter's 128-bit totals are ample.
[Derivation and exact recurrence](experiments/exact_math.md)

A further exact pruning experiment requires the unused patterns' directed
graph components to be partitionable into trails of the remaining row
lengths. It reproduced complete prefix counts of 138 and 36, but its measured
CPU time did not reliably improve on the existing search. It remains an
[experimental implementation](experiments/exact_math_search.cpp); the
earlier solver was not changed.

## Continuing the unrestricted computation

A second investigation implements
[adaptive colored exact cover](experiments/exact_cover_results.md), including
cell propagation, matching-based filtering, and multiplication of independent
components. It reproduces the known exact counts and significantly reduces
search nodes in selected prefixes, but the bounded unrestricted searches
remain incomplete. [Stronger marginal CNFs](experiments/exact_marginal_notes.md)
also preserve those counts without a demonstrated overall speed improvement.
An independent [bottom-up diagonal counter](experiments/exact_diagonal_results.md)
reproduces the binary and selected-prefix counts, but likewise does not exhaust
the unrestricted ternary instance.

An [exact last-row dynamic program](experiments/exact_lastrow_results.md)
does aggregate identical suffix problems across different upper boards. It
passes all 65,536 binary four-row prefixes and 31 ternary nine-row prefixes.
However, in the fully exhausted 138-board fiber, all final-row work occupies
only 0.19% of CPU time. Caching has little reuse there and increases its own
cost. This identifies a bottleneck in the earlier rows of that search; it is
not an impossibility result for other counting algorithms.

An important startup issue was identified in the full-symmetry CNF model:
it stalled while finding an initial satisfying assignment, before counting.
The earlier palette-only model had reached counting, so the issue did not
affect every previous trial. A bijective Boolean-variable transformation now
makes a known valid board the all-false assignment while preserving the
entire model set. The unrestricted full-symmetry runs consequently reach
the actual counting phase. [Proof, checks, and reproduction](experiments/exact_phase_notes.md)
The baseline phased run reached a 600-second wall limit without an exact
total. Its [terminal result](experiments/exact_phase_run.json) records the
input hash and explicitly leaves the count unknown.

Three further [preprocessing configurations](experiments/exact_config_notes.md)
all preserve binary orbit count 42. Two recover the known prefix-C count of
two, and one reduces the unrestricted formula to 9,802 variables before
counting. None finishes the full ternary count within its recorded limit.
Enabling tree decomposition alone does not resolve the problem: the full
formulas exceed this solver build's graph-size threshold.

The independent [d4 backend](experiments/exact_backend_notes.md) uses GMP
integer arithmetic and reproduces the raw binary count 168, orbit count 42,
and prefix-C count two. Both full ternary trials entered counting and ended
at their 120-second wall limits without an exact count. Its recorded early
decisions show no component splitting; the precise eventual bottleneck is
not established by the logs.

An [interleaved two-row recurrence](experiments/exact_tworow_results.md)
consumes penultimate- and bottom-row patterns together, allowing bottom-row
constraints to prune earlier. It passes every binary three-row prefix,
84 repeated ternary symmetry images, and both complete C/P prefix fibers.
Its six-row integration did not finish within a 90-second wall guard.
Neither caching nor the different order demonstrates a general acceleration.

## An exact reduced system of pattern counts

Let `N(a,b,c,d)` be a quadruple's number of occurrences. A valid board has
every `N` equal to one. An equivalent system fixes the **16** counts on
`{0,1}^4` to one and **65** selected three-coordinate margins to three.
For the margin omitting coordinate `j`, retain just those triples whose
coordinates before `j` are 0 or 1; coordinates after it are arbitrary.
There are 27 + 18 + 12 + 8 such margins.

To prove sufficiency, take a pattern containing a 2 and choose its first
such coordinate. Its selected margin sums three counts to three. Replacing
that coordinate by 0 or 1 gives patterns with fewer 2s, already known by
induction to have count one. The remaining count must also be one.
[ExactMarginals.lean](ExactMarginals.lean) proves this argument and its
equivalence to the original `TBoards.Valid` predicate, for an arbitrary
board rather than a discovered family. [Build log](exact-marginals-lean-build.log)

The quadruple conditions cannot simply be dropped. An explicit well-formed
board has all **108** triple margins equal to three, but eight quadruples
are absent and eight are doubled. It even satisfies fifteen of the sixteen
binary-cube conditions; only `1111` is doubled.
[MarginalCounterexample.lean](MarginalCounterexample.lean) checks this
counterexample in Lean's kernel, and a separate Cartesian-coordinate audit
checks its [recorded rows](experiments/exact_structure_counterexample.json).
[Build log](marginal-counterexample-lean-build.log)

```sh
lake build ExactMarginals MarginalCounterexample
```

This supplies an alternative exact counting formulation, not the evaluated
ternary total. The [reduced CNF generator](experiments/exact_reduced_cnf.py)
implements the same equations, and all sixteen encoding checks passed.
Bounded unrestricted and prefix-C runs reached counting but did not finish.
[Proof, checks, and terminal results](experiments/exact_reduced_notes.md)

A second formulation compares every pair of T placements directly, sharing
Boolean variables for equal-colored cell pairs. It reduces the unrestricted
normalized model to 5,382 variables and 50,363 clauses. All 27 exact-count
checks passed, but both bounded ternary runs remained incomplete, including
the selected prefix whose count is already known. This is another equivalent
model, not evidence of a faster full enumeration.
[Comparison encoding and results](experiments/exact_compare_notes.md)

The [structural investigation](experiments/exact_structure.md) also supplies
explicit obstructions to a direct BEST-theorem or determinant shortcut.
Local output permutations need additional compatibility conditions arising
from neighboring rows; their acceptance cannot be replaced by last-exit or
boundary-sign data alone.

## Exact geometric inclusion–exclusion

A [Möbius aggregation](experiments/exact_mobius_report.md) assigns each
collision of two placements four cell-equality constraints. Grouping
partitions that force the same cell equalities gives an exact polynomial
`P_h(q)` for boards of height `h` with distinct T patterns. The desired
number is `P_10(3)`. Two independent implementations evaluate the polynomials
through height four and agree with the earlier board census.

The full closure table is too large for straightforward materialization:
17 disjoint T placements induce a partition-lattice interval containing
82,864,869,804 nonzero Möbius states. This bound does not exclude symbolic
summation: that interval alone has the compact sum `q^32 (q^4)_17`.
However, explicit examples show that cell-component counts and size
multisets lose geometric information needed for subsequent collisions.
The report proves and checks these precise limitations rather than treating
the finite sum as an evaluated answer.

## Exact parity characterization

There is also an exact parity formulation. If each of the 81 possible
patterns occurs an odd number of times, every count is positive. The board
has only 81 placements, so all counts must equal one. Conversely every valid
board satisfies those parity equations.

[ExactParity.lean](ExactParity.lean) proves
`TBoards.ExactParity.valid_iff_odd` for the original validity predicate. It
also proves the saturation argument using mere presence of every pattern.
The more general `valid_iff_congruent_one` proves that every pattern count
being congruent to one modulo any integer greater than one is also equivalent
to validity; primality is unnecessary for this counting argument.
The [build log](exact-parity-lean-build.log) records a successful kernel-checked
build with only standard logical axioms.

```sh
lake build ExactParity
```

The [parity CNF implementation](experiments/exact_parity_notes.md) passes
functional-gate and exact small-count checks. Both full ternary variants and
both prefix-C trials timed out without a count. The installed counter rejects
native XOR input; these were clause-circuit trials, so they do not establish
the performance of a Gaussian or polynomial-algebra method.

The [algebraic derivation](experiments/exact_parity_math.md) gives 80 Boolean
moment equations of degree at most four. Four whole-cell eliminations leave
192 Boolean variables; all reconstructed-cell palette conditions are retained.
The binary analogue was exhausted over all 2^21 reduced assignments and agrees
with geometric checking on every assignment, giving exactly 168 solutions.

A Fourier change of coordinates gives a more compact ordinary polynomial
ideal: encode colors by the three nonzero elements of F4, impose `z_i^3+1=0`,
and require 40 representative nonconstant Fourier moments to vanish.
Frobenius gives the other 40 moments. All coefficients lie in F2, so the ideal
can be computed over F2 without restricting variables to Boolean values.
After four linear eliminations it has 96 variables and 136 generators.

Its quotient vector-space dimension is exactly the unrestricted labeled
count: over F4 the squarefree domain quotient is a product of fields indexed
by all ternary boards, and the moment equations retain exactly the valid
factors. Extending scalars from F2 to F4 preserves that dimension. The
[explicit original ideal](experiments/exact_parity_math_fourier_original.sing)
and [reduced export](experiments/exact_parity_math_fourier_reduced.json) have
passed checks on 322 valid boards and substitution checks. Their quotient
dimension has not been evaluated. An
[independent review](experiments/exact_parity_review_fourier.md) also verified
every reduced polynomial symbolically, confirmed the retained domain
conditions, and found no multiplicity or symmetry factor. The exact algebra
[backend](experiments/exact_algebra_backend_results.md) reproduced known
nine-row fibers with counts one and six. Singular's arbitrary-precision
Hilbert calculation and two independent standard-monomial counters agreed,
including an arithmetic fixture of dimension 10^20. The one full reduced
trial exhausted its 2 GiB memory allowance before completing a standard basis;
its 90-second wall guard subsequently expired. It produced no total.

Completed bases are exported before Hilbert evaluation, so a slow Hilbert
stage cannot lose an otherwise usable basis. The
[independent monomial counter](experiments/exact_standard_monomials.md) uses
arbitrary-precision arithmetic and requires a completed-standard-basis
attestation. Leading terms of arbitrary polynomial generators are not accepted
as an exact quotient count.

The [prime-characteristic extension](experiments/exact_parity_math_prime.md)
proves the same quotient-dimension identity for every prime `p = 2 mod 3`,
using domains `z_i^3-1` and the original integer Fourier sums reduced modulo
`p`. Characteristic 29 makes the unary equations alone enforce exact color
histograms; characteristic five already enforces exact triple margins at the
triple layer. These are stronger intermediate constraints, not a proof of
faster counting. The [fresh geometric generator](experiments/exact_prime_fourier.py)
avoids reusing characteristic-two substitutions and supports explicitly
including all 80 nonconstant moments as redundant generators.

This redundancy helped a known fixed-prefix problem: the six-completion
nine-row fiber finished over characteristic 29 with all 80 moments, and the
Hilbert calculation and both monomial counters returned six. However, neither
unrestricted characteristic-29 run completed a basis: both `std` and `slimgb`
exhausted the 2 GiB memory allowance. They used the same 100-variable ideal
with all 180 generators and no fixed cells or normalization. Two independent
input audits checked the full model; the
[recorded prime-field results](experiments/exact_algebra_backend_prime_results.md)
distinguish the completed fixed fiber from these failed unrestricted trials.

An [independent msolve F4 backend](experiments/exact_msolve_notes.md) uses
exact prime-field linear algebra and the same two arbitrary-precision
monomial counters. Its narrowly patched export path avoids msolve's later
machine-integer staircase enumeration; small basis exports match the stock
solver exactly, including an arithmetic fixture of dimension 3^100. The
known six-completion board fiber is also reproduced. Two unrestricted
characteristic-29 trials timed out before exporting a basis. A
characteristic-two trial finished one degree-four matrix but failed while
allocating the subsequent basis hash. None produced an unrestricted count.

A reviewed support-only import patch avoids retaining unused matrix
columns. A further [audited variable permutation](experiments/exact_parity_math_pivot_audit.md)
places the four dispersed linear pivots first; no T contains more than one
of these pivots. The reordered input retains every equation and reproduces
the known six-completion fiber. Its full trial completes one additional
degree-four round, but again exhausts the 2 GiB memory allowance before
exporting a basis. This is progress in the calculation, not an evaluated
total; the [backend report](experiments/exact_msolve_notes.md) records the
terminal results and exact input hashes.
The explicit 96-variable export is also now supported by this backend, with
either 36 representative moments or all 72 nonzero substituted moments.
An [independent actual-input audit](experiments/exact_parity_math_reduced_input_audit.md)
rederives the substitution geometrically and verifies that all four
eliminated-cell cubic domains remain present. Both exports retain the full
unrestricted count, with no symmetry or coefficient-extension factor.
Further reviewed allocation changes pass the earlier storage boundary but
encounter a null allocation during the following linear-algebra round,
confirmed by debugger registers and disassembly. Reducing the pair-batch
target to one avoids that crash within a 180-second trial, which nevertheless
times out in degree four with no completed basis. A proposed retry with a
3 GiB memory cap was prevented from starting by its available-memory check.
No result from these trials is an exact total or an exact zero.

A separate [signed-permutation investigation](experiments/exact_sign_math.md)
rules out a particular determinant shortcut. Horizontal reflection reverses
the sign of the 81-pattern permutation, so the unrestricted signed sum is
exactly zero. Two certified canonical boards share their first nine rows and
all 19 rotor-boundary colors yet have opposite signs. A universal six-board
identity also rules out fixed products of per-cell/color weights that make
all unrestricted terms positive or equal. A separate 56-board XOR certificate
rules out real sign corrections of that factorized form even on canonical
representatives. These are exact obstructions to those specific shortcuts,
not an exclusion of every determinant or Pfaffian approach. The embedded
certificates pass independent inversion/cycle sign and geometric checks.

A [rotor scheduling audit](experiments/exact_rotor_abelian.md) also gives a
specific obstruction to an abelian-network shortcut: with the same boundary
and local permutations, swapping two independent ready updates can change
completion into capacity failure. Re-encoding the permutations for a new
legal schedule nevertheless gives a bijection of accepted tuples, including
for deterministic adaptive schedulers that inspect only revealed data.
This preserves exact counting across schedules; it supplies no evaluated
total or runtime improvement.

## Redundant elementary color-balance equations

The [elementary-symmetric audit](experiments/exact_parity_math_elementary.md)
adds exact unary histogram information as low-degree algebraic consequences.
For each role, the 81 colors comprise 27 copies of each nonzero F4 element,
so their generating polynomial is `(1+t^3)^27`. In particular its quadratic
elementary coefficient is zero. One whole-role quadratic and three sparse
boundary differences give four additional equations; their Frobenius
partners may also be included.

All 3,403 possible triples of nonnegative color counts summing to 81 were
checked independently. The power-of-two coefficients `e1,e2,e4,e8,e16`
vanishing force exactly `(27,27,27)`; `e1=e2=0` already forces each count
congruent to three modulo four. The first augmentation uses only
the four `e2` equations and their Frobenius partners, not all five layers.
Ordinary squared variables are retained. The new quadratics add independent
low-degree consequences to the existing reduced model. Radicality of the
cubic-domain quotient proves that these generators leave the complete
Fourier ideal, hence the unrestricted quotient dimension, unchanged.

An [audited change to cumulative-sum coordinates](experiments/exact_pivot_review_prefix_notes.md)
substantially reduces the size of these equations. Order cells by their
membership in the four roles and set `y_j = z_0 + ... + z_j` in that order.
The inverse is `z_j = y_j + y_(j-1)`. The four unary equations then have
only 1, 2, 4 and 5 terms; eliminating four prefix variables leaves an
isomorphic 96-variable quotient. The transformed 100 color-domain cubics
have 532 terms in total, and the eight elementary equations have 616.

Prefix variables can equal zero. The exporter therefore retains the
transformed original color cubics, rather than imposing individual
`y_j^3+1` domains. Optional `y_j^4+y_j` equations are explicit consequences
of those cubics. Independent checks rebuild every polynomial, verify the
coordinate inverse, and check all eight export options. The full model
with a known nine-row prefix appended reproduces its six completions;
this is a validation case, not the unrestricted count. The unrestricted
run reaches degree five but fails a checked monomial-storage allocation
under a 3 GiB cap, before exporting a basis or count. Its
[terminal audit](experiments/exact_msolve_notes.md) preserves that distinction.

A further [quartic augmentation](experiments/exact_pivot_math_prefix_e4.md)
adds the next histogram layer, `e4=0`, with 14,194 terms and no auxiliary
variables. One whole-role equation and three boundary differences suffice;
explicit polynomial identities justify the differences using the retained
unary, quadratic and cell-domain equations. Independent product expansion
checks all four quartics. Together the first three layers force each role's
color counts to be three modulo eight. No `e8` or `e16` constraints have
been added to the solver model.

## An exact model over the three-element field

The [natural F3 formulation](experiments/exact_f3_math.md) uses the actual
palette `0,1,2` and individual field equations `z^3-z=0`. For each nonzero
exponent tuple in `{0,1,2}^4`, sum the corresponding color product over all
81 placements. Every target is zero except the all-two tuple, whose target
is one. The indicator `1-(z-c)^2` shows that these equations make every
pattern count congruent to one modulo three. Each count is therefore
positive, and the 81 available placements force all 81 counts to equal one.

[ExactNativeMoments.lean](ExactNativeMoments.lean) kernel-checks this exact
equivalence for the original board predicate, using precisely the 80 power
sums over actual geometric placements. Its proof includes the finite
inverse transform, modular-count saturation and the automatic constant
moment; it uses only Lean's standard axioms. The algebraic dimension
calculation remains a separate computational step.

```sh
lake build ExactNativeMoments
```

In characteristic three, linear coordinate changes preserve the individual
field-domain ideal. The signed cumulative-sum transformation and four unary
eliminations consequently need only 96 independent field cubics, together
with 76 remaining moments. There are no substituted pivot domains or
coefficient-extension factors; the quotient dimension is exactly the full
labeled count. Independent geometric expansion checks all 172 generators.
A separate fixed-prefix run reproduces six completions directly over F3.

Four additional [role-histogram cubics](experiments/exact_f3_math_e3.md)
require just 574 terms and no new variables. Explicit identities prove
they are redundant consequences of full validity, with the existing unary
quadratic moments justifying the sparse boundary differences. These are
separate from the characteristic-two histogram equations. Neither exact
formulation by itself evaluates the unrestricted count.
The full F3 trial reaches degree five and successfully uses the reviewed
temporary-storage compaction, but then fails another exponent-table
allocation under its 3 GiB cap. Its
[independent terminal audit](experiments/exact_f3_terminal_review_results.json)
records no completed basis or count.

An [exact translation factorization](experiments/exact_f3_translation.md)
separates the global color shift. It leaves 95 coupled coordinates and one
independent apex-color variable satisfying `a^3-a=0`. Triangular binomial
identities prove equality of the moment ideals before and after this change.
The independent variable remains in the exported ring, so its quotient
dimension already includes all three shifts and still equals the full
labeled count; no external multiplier belongs on this export.
The translated model reproduces the known six-completion prefix, with the
actual apex condition fixing the offset. Its subsequent unrestricted trial
times out after 300 seconds with no basis or count; the smaller-growth
allocator records no allocation error in that run.

An [independently checked variable permutation](experiments/exact_f3_order.md)
preserves every equation and the independent offset factor. It improves a
monomial-cooccurrence graph heuristic; the full polynomial-support graph
remains complete, so the graph calculation establishes no decomposition or
solver-runtime guarantee.

The same native-F3 model was also tried with
[Singular's two standard-basis algorithms](experiments/exact_native_singular.md).
Both exhausted a 3 GiB memory allowance without completing a basis: `slimgb`
after about 42 seconds and `std` after about 67 seconds. Both reproduced the
known six-completion prefix before the unrestricted trials; those checks do
not supply the full count.

A narrowly scoped [checked byte-exponent build](experiments/exact_msolve_byte_review_notes.md)
halves the exponent-vector storage used by these F3 models. It retains
ordinary polynomial arithmetic and rejects overflow before narrowing.
Independent complete-basis comparisons, finite-field enumeration and
sanitizer boundary tests passed. This is a storage improvement, not a
completed count.

A further [exact sign factorization](experiments/exact_f3_sign.md) selects
one normalized board from each global-negation pair with a degree-five
polynomial. An independent two-valued sign and the existing three-valued
offset recover every original board uniquely. Both factors remain inside
the exported 97-variable ideal, whose dimension is still the full count.
The added constraint has 180 terms and introduces a nonzero target at degree
five. Its effect on the full calculation remains to be measured.
An independently checked fixed-prefix run reproduces six completions using
the new bilinear color reconstruction.

An alternative [four-branch partition](experiments/exact_f3_sign_branches.md)
uses only linear equations to choose the first nonzero difference between
two distinct patterns. Every valid board belongs to exactly one branch;
the color-shift and sign factors remain inside each branch's quotient.
The unrestricted count is the sum of all four completed branch dimensions.
Two variable orders of the same branch are alternatives and must not both
be added. Missing or unfinished branches remain unknown, not zero.
Independent solver fixtures reproduce branch dimensions `6,0,0,0` for the
known nine-row prefix, with both integer counters agreeing. These completed
fixtures do not evaluate the four unrestricted branches.

An [affine elimination](experiments/exact_f3_branch_elimination.md) removes
the solved branch coordinates, leaving 96, 95, 94 and 93 variables. Explicit
identities preserve every original field domain; independent substitution
checks cover every moment and histogram equation. These are alternative
representations of the same four branches, with the same sum rule.
The reduced models independently reproduce the known-prefix dimensions
`6,0,0,0` as well.

A separate full-label Boolean encoding of branch 3 adds only 21 direct
equality/inequality clauses to the existing parsimonious CNF. An exhaustive
2,187-assignment check verifies the added relation. Its bounded deterministic
GANAK trial timed out after 60 seconds without a count or satisfiability
conclusion; the artifacts are `experiments/exact_f3_branch3_ganak.*`.

## The remaining obstacle

To obtain the unrestricted total, an algorithm must count extensions of
**every** admissible prefix, or replace that enumeration with an equivalent
evaluated formula. Neither more witnesses, nor an exact count for selected
prefixes, nor a count of locally admissible caps establishes that total.
The new tools make those distinctions explicit. No unrestricted ternary
search has reported completion.

A literature check also examined Condon, Dugan, Goldman and Williams,
[Polyomino Density](https://arxiv.org/html/2608.29231v1) (August 2026).
Its formulas concern minimum uncolored board sizes and its later sections
give colored constructions; it supplies no enumeration formula for this
ternary board. Those geometric density results do not evaluate the count
investigated here.
