# Rigorous upper bounds from the existing equations

The useful improvement is the independent four-row rotor bound

\[
N\le 1,185,818,059,470,602,086,065,654,202,368.
\]

The prior bound was `3^19 * 6^27 = 1189563417824350846613100429312`.
Their ratio is exactly `706357/708588`, a reduction of about 0.31485%.
The certified lower bound remains **45,083,592**. These audits produce no new
valid boards or larger lower bound, and the exact count remains unknown.

## Polynomial leading-monomial relaxation

Let `I` be any of the audited ordinary F3 board ideals, and let `f_i` be its
known generators, including the field domains and proved redundant equations.
For degree reverse lexicographic order with `x1 > ... > xn`, define the
**separate monomial ideal** `J = <LM(f_i)>`. Then `J ⊆ in(I)`, so

`N = dim(F3[x]/I) ≤ dim(F3[x]/J)`

for a full model, or the corresponding branch count satisfies this inequality
for a branch model. Field domains make these dimensions finite. The finite-field
model proofs justify the equality between the board count and the dimension of
the original quotient; the order/affine transformations preserve that count.

Every monomial generating set is a Gröbner basis **of its own monomial ideal**.
This is the only completed-basis attestation passed to the two staircase
counters. Nothing asserts that the polynomial source generators form a
Gröbner basis of `I`. JSON records explicitly set
`source_polynomial_basis_complete=false` and `exact_board_count=null`.

`exact_polynomial_upper.py` reads hash-pinned exports through their audited
helpers, collects coefficients modulo 3 before choosing each leading monomial,
checks every ordinary cubic field domain, and uses both independent Python
integer counters. Each counter has a 15-second wall limit, each child a 768 MiB
address-space limit and a 40-second CPU limit. All 13 models completed, with
the two counters agreeing. No polynomial solver ran. A small deliberately
incomplete polynomial fixture has two actual roots but relaxation dimension
five, explicitly testing the distinction between a bound and an exact count.

The best full-model relaxation, translated with minimum-fill variable order, is

`443509852422827461048999901549706292982846964`.

The best bounds per affine-eliminated branch, choosing the smaller natural or
minimum-fill result for each *same* branch, are:

| Branch | Upper bound | Chosen order |
|---|---:|---|
| 0 | 337050247419485981088744337232138310119131512 | minimum-fill |
| 1 | 124131037412803021168233208597002344391700608 | natural |
| 2 | 50428233948951227349594740992532202409128372 | natural |
| 3 | 13361326943739214084080657869816224569939996 | natural |

Their sum is `524970845724979443690652944691489081489900488`.
Both it and the best full-model relaxation are far larger than the rotor bound,
so **these polynomial bounds do not improve the current upper bound**. Natural
and permuted representations are alternatives, never disjoint terms to add.
Offset/sign factors are already retained; no additional factor is applied.
All results, leading monomials, source hashes and counter statistics are in
`exact_polynomial_upper_results.json`.

## Independent rotor verification

`exact_rotor_upper_review.cpp` separately enumerates all `3^15 = 14,348,907`
four-row caps with apex zero, without the owner's recursive pruning. It builds
the nine T placements from centered Cartesian row coordinates, tests the nine
quadruples for distinctness, and counts how often each input triple appears.
Its 9,391,598 accepted caps match every one of the owner's ten histogram bins.

A valid full board has a permutation of the three output colors for each of
the 27 input triples `(top,left,middle)`. Row-major decoding uses the 19 boundary
cells (apex and first two cells of each later row) and these 27 permutations.
This gives an injection from valid boards into rotor parameter tuples.

A four-row cap fixes seven boundary cells. If it uses a triple `k` times, it
fixes the first `k` distinct entries of that triple's permutation; precisely
`(3-k)!` choices remain. Every matching choice of unused boundary values and
permutation suffixes decodes to this cap, irrespective of later acceptance.
Therefore its full parameter fiber has size `3^12 * product((3-k)!)`.
The independent histogram gives

`sum_apex0_caps 6^n0 * 2^n1 = 743775294887298299068416`.

Multiplication by `3^12` for the remaining boundary and by 3 to restore the apex
gives the upper bound above. There is no reflection or palette-orbit divisor.
The result and provenance are `exact_rotor_upper_review_results.json`.

## Failed solver runs and a possible later diagnostic

`exact_polynomial_upper_artifact_audit.py` checks the consolidated incomplete
trials plus every terminal `exact_msolve_full*.json` run. Their `.basis` files
are empty, `.leading.json` files absent, and export-completion marker counts
zero. The detailed inventory is
`exact_polynomial_upper_failed_artifacts_extended.json`; an earlier narrower
19-trial inventory is preserved separately. Matrix sizes, pivot counts, degrees
and allocation diagnostics are not polynomial or leading-monomial certificates.
No additional bound can be extracted from those logs alone.

A future diagnostic could write a **separate partial-ideal-member LM snapshot**
after successful ordinary `compute_new_elements`/`update` rounds, when rows have
been converted back into the basis hash table. This is a proposal only: no
solver source, backend acceptance gate, or binary changed for this audit.

The minimal safe format would pin the exact input, executable, field, variable
order, coordinate map and round number, and export the actual leading exponent
vector of each retained known ideal member through the reviewed stored-vector
accessor. Include the original field-domain LMs independently, and write a
complete snapshot footer/atomic rename only after all vectors are checked.
Keep this file and its marker distinct from the completed-basis export. Its
schema must say `source_polynomial_basis_complete=false` and allow only the
upper-bound route `J ⊆ in(I)`, never the exact-count aggregator.

The mathematical justification would still depend on the reviewed exact F4
operations producing genuine ideal members; leading exponents alone are not
an independent ideal-membership certificate. Stronger verification could retain
full polynomial/member certificates, at much greater output cost. A later crash
does not turn missing snapshots or incomplete output into zero counts. Any
accepted earlier snapshot would need its own complete serialization and
provenance audit. The proposed diagnostic has not been implemented or tested.
