# Rigorous upper bounds from the existing equations

The useful new bound is the independent four-row rotor upper bound:

\[
N\le 1,185,818,059,470,602,086,065,654,202,368.
\]

The prior bound was `3^19 * 6^27 = 1189563417824350846613100429312`. Their
ratio is `706357/708588`, a drop of about 0.31485%. The certified lower bound
stays **45,083,592**. These audits find no new valid boards and no larger lower
bound, and the exact count remains unknown.

## Polynomial leading-monomial relaxation

Let `I` be any audited ordinary F3 board ideal with known generators `f_i`
(including field domains and proved redundant equations). Under degree reverse
lexicographic order with `x1 > ... > xn`, form the **separate monomial ideal**
`J = <LM(f_i)>`. Since `J ⊆ in(I)`,

`N = dim(F3[x]/I) ≤ dim(F3[x]/J)`

for a full model (and likewise for a branch count on a branch model). The field
domains keep both dimensions finite. The finite-field proofs establish that the
original quotient dimension equals the board count, and the variable-order and
affine transformations preserve that count.

Any set of monomial generators is automatically a Gröbner basis **of its own
monomial ideal**, and that is the only completed-basis attestation passed to
the two staircase counters. Nothing claims that the source polynomials form a
Gröbner basis of `I`. Every JSON record explicitly sets
`source_polynomial_basis_complete=false` and `exact_board_count=null`.

`exact_polynomial_upper.py` loads hash-pinned exports through their audited
helpers, collects coefficients modulo 3 before taking leading monomials, checks
every ordinary cubic field domain, and runs both independent Python integer
counters (15-second wall limit per counter, 768 MiB address-space limit and
40-second CPU limit per child). All 13 models finished with both counters
agreeing, and no polynomial solver ran. A small intentionally incomplete
polynomial fixture has 2 actual roots but relaxation dimension 5, directly
testing the gap between an upper bound and an exact count.

The best full-model relaxation (translated, minimum-fill variable order) is

`443509852422827461048999901549706292982846964`.

Taking the smaller of the natural or minimum-fill bound for each *same*
affine-eliminated branch gives:

| Branch | Upper bound | Chosen order |
|---|---:|---|
| 0 | 337050247419485981088744337232138310119131512 | minimum-fill |
| 1 | 124131037412803021168233208597002344391700608 | natural |
| 2 | 50428233948951227349594740992532202409128372 | natural |
| 3 | 13361326943739214084080657869816224569939996 | natural |

These four branch bounds sum to `524970845724979443690652944691489081489900488`.
Both the branch sum and the best full-model bound are far above the rotor
bound, so **these polynomial relaxations do not tighten the current upper
bound**. Natural and permuted models are alternative views of the same branch,
never disjoint terms to add. Offset and sign factors are already built into
each quotient, so no extra factor is multiplied in. Full results, leading
monomials, source hashes, and counter stats are in
`exact_polynomial_upper_results.json`.

## Independent rotor verification

`exact_rotor_upper_review.cpp` enumerates all `3^15 = 14,348,907` four-row caps
with apex 0 directly, without the owner's recursive pruning. It builds the nine
T placements from centered Cartesian coordinates, checks that all nine
quadruples are distinct, and counts how often each input triple occurs. Its
9,391,598 accepted caps match all ten of the owner's histogram bins.

Every valid board determines a permutation of the three output colors for each
of the 27 input triples `(top, left, middle)`. Row-major decoding uses the 19
boundary cells (the apex plus the first two cells of each later row) together
with those 27 permutations, injecting valid boards into rotor parameter tuples.

A four-row cap fixes 7 boundary cells. If it uses a triple `k` times, it fixes
the first `k` distinct outputs of that triple's permutation, leaving `(3-k)!`
choices for the rest. Every choice of the remaining 12 boundary cells and
unused permutation suffixes decodes back to the same cap, whether or not the
full board succeeds. So each cap has full parameter fiber size
`3^12 * product((3-k)!)`. The independent histogram yields

`sum_apex0_caps 6^n0 * 2^n1 = 743775294887298299068416`.

Multiplying by `3^12` for the remaining boundary cells and by 3 for the apex
gives the bound above, with no reflection or palette-orbit divisor. The result
and provenance are saved in `exact_rotor_upper_review_results.json`.

## Failed solver runs and a possible later diagnostic

`exact_polynomial_upper_artifact_audit.py` inspects the consolidated incomplete
trials and every terminal `exact_msolve_full*.json` run. Every `.basis` file is
empty, every `.leading.json` file is missing, and all export-completion marker
counts are zero. See `exact_polynomial_upper_failed_artifacts_extended.json`
(an earlier 19-trial inventory is kept separately). Matrix dimensions, pivot
counts, degrees, and allocation logs are not polynomial or leading-monomial
certificates, so no extra upper bound can be extracted from those logs alone.

A future diagnostic could write a **separate partial-ideal-member LM snapshot**
after completed ordinary `compute_new_elements`/`update` rounds, once rows have
been written back into the basis hash table. This is only a proposal: no solver
source, acceptance gate, or binary was modified here.

A safe snapshot format would pin the input, executable, field, variable order,
coordinate map, and round number, and export each retained ideal member's
leading exponent vector through the reviewed stored-vector accessor. It would
include the original field-domain LMs independently and write a complete footer
via atomic rename only after checking every vector. The file and marker must
stay separate from completed-basis exports, set
`source_polynomial_basis_complete=false`, and feed only the upper-bound route
`J ⊆ in(I)`, never the exact-count aggregator.

That bound would still rely on the reviewed exact F4 steps producing valid
ideal members, since leading exponents by themselves are not an independent
ideal-membership proof (storing full polynomial certificates would cost much
more output). A later crash never turns missing snapshots or incomplete output
into zero counts, and any saved earlier snapshot would need its own
serialization and provenance audit. None of this diagnostic is implemented or
tested yet.
