# Investigation of the exact ternary count

**The unrestricted exact count has not been obtained.** When this
investigation began, the certified bound was
[32,155,680 labeled boards](SPLICE_RANGES.md). The work
below supplies a global symmetry theorem, exhaustive smaller computations,
and reproducible exact counting programs. It does not convert the earlier
selected-prefix searches into an exhaustive ternary enumeration.

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
The twelve-image statement is the mathematical group-action corollary;
the file's formal conclusion is the trivial-stabilizer statement.

```sh
lake build ExactSymmetry
```

The [build log](exact-symmetry-lean-build.log) records a successful build and
only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

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

## The remaining obstacle

To obtain the unrestricted total, an algorithm must count extensions of
**every** admissible prefix, or replace that enumeration with an equivalent
evaluated formula. Neither more witnesses, nor an exact count for selected
prefixes, nor a count of locally admissible caps establishes that total.
The new tools make those distinctions explicit. No unrestricted ternary
search has reported completion.
