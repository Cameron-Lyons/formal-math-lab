# Investigation of the exact ternary count

For the number *N* of valid labeled three-color T boards, the tightest verified bounds are:

**45,083,592 ≤ N ≤ 1,185,818,059,470,602,086,065,654,202,368.**

See the [lower-bound certificate](SplicePalCertificates.lean), the [four-row upper-bound census](experiments/exact_rotor_upper_results.json), and the [independent upper-bound audit](experiments/exact_rotor_upper_review_results.json).

## A global symmetry theorem

Every valid ternary board has **12 distinct images** under the six color permutations and horizontal reflection. This holds for all valid boards, not just the ones in our certificates.

Because a board is valid, the map from its 81 placements to the 81 ordered patterns is a bijection. Any recolored reflection that fixed the board would pair fixed placements with fixed patterns. Reflection fixes 9 placements, whereas each recolored reflection fixes 27, 3, or 0 patterns, never 9. An unreflected color permutation fixes all 81 placements, and only the identity fixes all 81 patterns. So the stabilizer is trivial, and composing and inverting these transformations gives an orbit of size 12.

[ExactSymmetry.lean](ExactSymmetry.lean) proves `TBoards.ExactSymmetry.stabilizer_trivial` in Lean's kernel from `Valid b` alone, with no assumptions on the cap, pivot, or provenance. From the same hypothesis, [ExactOrbit.lean](ExactOrbit.lean) proves `TBoards.ExactOrbit.twelve_distinct_images`: the list `orbit b` has length 12, contains no duplicates, and consists of valid boards. It also proves `TBoards.ExactOrbit.length_eq_twelve_mul_canonical`: any duplicate-free list of valid boards closed under all 12 symmetries has length 12 times the sublist picked by any selector choosing one image per orbit. The list of all valid boards satisfies these hypotheses, though Lean does not formalize whether a given solver's canonical-form clauses define such a selector or match `Valid`.

```sh
lake build ExactSymmetry ExactOrbit
```

The build logs for the [stabilizer theorem](exact-symmetry-lean-build.log) and the [twelve-image corollary and counting step](exact-orbit-lean-build.log) confirm clean builds using only `propext`, `Classical.choice`, and `Quot.sound`.

A separate [finite-rank argument](experiments/exact_structure_gauge.md) shows we cannot enlarge this symmetry group by applying fixed independent color permutations at individual cells: if such a map preserves all valid boards, all 100 cell permutations must be equal. Just 322 explicit valid boards force this via 160 XOR identities and an independently checked rank-161 certificate (not formalized in Lean).

That same note shows that the only cell permutations preserving the uncolored T-incidence structure are the identity and horizontal reflection. Combined with fixed cellwise recolorings, these give the known 12 symmetries. This still allows board-dependent maps or spatial permutations that preserve valid boards without preserving T-incidence.

An [exhaustive symmetry split](experiments/exact_parity_math_symmetry.md) expresses the full count either as 3 times the apex-zero count or as a weighted sum over ten top-two-row fibers whose orbit weights sum to 81 (not uniformly 12). The [manifest and strict aggregation audit](experiments/exact_symmetry_split_notes.md) reproduce the binary count of 168 and refuse to report a ternary total until every fiber has an audited complete count. Global cubic homogeneity only recovers the apex factor of 3. A characteristic-29 apex-zero algebra run ran out of its 2 GiB memory cap before finishing a basis or count.

The [msolve cap auditor](experiments/exact_msolve_cap_split_notes.md) supports the same ten-case sum with explicit coefficient-extension divisors and input/basis provenance checks. Its geometry audit checked all ten models in characteristics 2 and 29. The first four-cell case (`0000`) timed out after 180 seconds with no basis, so no cap counts have finished yet.

## Exact algorithms and their measured limits

The [row-transfer census](experiments/exact_algo_frontier.cpp) merges prefixes that share the same last row and used-pattern set. With the apex fixed to 0, there are 9,391,598 valid four-row prefixes and 9,379,134 distinct transfer states. Merging removes only about 0.13% of states at this depth, so plain state-table DP does not compress enough for a full count.

The [streaming counter](experiments/exact_algo_count.cpp) runs over deterministic prefix intervals, marks each run `COMPLETE` or `INCOMPLETE`, and drops partial counts from unfinished intervals so completed intervals can be added safely without mistaking a timeout for an exact count. The [cap census wrapper](experiments/exact_algo_census.py) groups prefixes into explicit symmetry orbits and weights each by its actual orbit size, since partial caps can have nontrivial stabilizers (multiplying by 12 would overcount).

That census exhausted all 1,572 three-row prefix orbits in about 189 seconds and counted **198,649,032,096 five-row caps** with 16 distinct T patterns. These are 25-cell partial boards and may not extend to full 100-cell boards. Every prefix, orbit size, and completion count is saved in [exact_algo_census_results.json](experiments/exact_algo_census_results.json), and the [counter report](experiments/exact_algo_results.md) details the scope, orbit weights, and independent checks.

```sh
python experiments/exact_algo_census.py --seconds 300
```

The [CNF model](experiments/exact_count_cnf.py) preserves exact counts: cell variables specify the board and auxiliary variables are uniquely forced. Deterministic model counting reproduced the binary total of **168** and the **2** completions of a published seven-row ternary prefix. Full symmetry breaking picks **42** binary orbits and was checked on all 17,160 images of the earlier 1,430 ternary representatives; with `--orbit-canonical`, the ternary count multiplies by 12. Three bounded ternary runs timed out without a count: a six-row prefix (60 s), an unrestricted run with color breaking (120 s), and an unrestricted run with full symmetry breaking (60 s). See [exact_count_notes.md](experiments/exact_count_notes.md) for the encoding, commands, and solver details.

An independent enumeration using [local output permutations](experiments/exact_math_rotors.py) also reproduced all 168 binary boards and matched the cell-by-cell enumerator board for board. Every valid ternary board is uniquely determined by 19 boundary colors and 27 permutations of the three output colors, subject to a deterministic acceptance test. That yields the upper bound:

```text
3^19 × 6^27 = 1,189,563,417,824,350,846,613,100,429,312.
```

Many parameter tuples fail the acceptance test, so this is far above the true count, though it confirms that 128-bit counters in the streaming solver will never overflow (see [exact_math.md](experiments/exact_math.md)).

Another exact pruning experiment requires the directed graph of unused patterns to split into trails matching the remaining row lengths. It reproduced the complete prefix counts of 138 and 36, but did not consistently beat the existing search in CPU time. It stays as [exact_math_search.cpp](experiments/exact_math_search.cpp), leaving the main solver untouched.

## Continuing the unrestricted computation

We also built an [adaptive colored exact-cover solver](experiments/exact_cover_results.md) with cell propagation, matching filters, and independent-component multiplication. It reproduces the known exact counts and cuts search nodes on several prefixes, while unrestricted bounded runs still time out. [Stronger marginal CNFs](experiments/exact_marginal_notes.md) also preserve exact counts without showing a net speedup. An independent [bottom-up diagonal counter](experiments/exact_diagonal_results.md) matches the binary and prefix counts too, yet still cannot exhaust the unrestricted ternary board.

An [exact last-row dynamic program](experiments/exact_lastrow_results.md) merges identical bottom-row subproblems across upper boards and passes all 65,536 binary four-row prefixes plus 31 ternary nine-row prefixes. Still, in the exhausted 138-board fiber, last-row work takes only 0.19% of CPU time, so caching sees little reuse and adds overhead. The bottleneck in that search sits in earlier rows, though other algorithms might behave differently.

We hit a startup bottleneck in the full-symmetry CNF model: the solver got stuck searching for a first solution before counting even began (the earlier palette-only model had not hit this). A bijective Boolean variable flip turns a known valid board into the all-false assignment without changing the solution count, allowing full-symmetry runs to reach the counting phase ([exact_phase_notes.md](experiments/exact_phase_notes.md)). Even then, a 600-second baseline run timed out without a count, recorded with its input hash in [exact_phase_run.json](experiments/exact_phase_run.json).

Three more [preprocessing configurations](experiments/exact_config_notes.md) keep the binary orbit count at 42; two recover the prefix-C count of 2, and one shrinks the unrestricted formula to 9,802 variables before counting. None finished the unrestricted ternary count within its time limit. Turning on tree decomposition did not help because the full formulas exceed this solver build's graph-size limit.

The independent [d4 backend](experiments/exact_backend_notes.md) uses GMP big integers and reproduces the raw binary count 168, orbit count 42, and prefix-C count 2. Both full ternary runs reached counting and hit their 120-second limits without a total. Early decision logs show no component splitting, though the logs do not pinpoint the final bottleneck.

An [interleaved two-row recurrence](experiments/exact_tworow_results.md) pairs the bottom two rows together so bottom-row constraints can prune earlier. It passes every binary three-row prefix, 84 ternary symmetry images, and both complete C/P prefix fibers, while its six-row integration hit a 90-second limit. Neither caching nor this ordering produced a general speedup.

## An exact reduced system of pattern counts

Let `N(a,b,c,d)` be how many times a quadruple appears on a board. A valid board has every `N` equal to 1. An equivalent system sets the **16** counts on `{0,1}^4` to 1 and sets **65** selected three-coordinate margins to 3: for the margin dropping coordinate `j`, keep only triples whose entries before `j` lie in `{0,1}` (giving 27 + 18 + 12 + 8 = 65 margins).

To see why this suffices, pick any pattern containing a 2 and look at its first coordinate equal to 2. Its selected margin sums three counts to 3. Changing that coordinate to 0 or 1 yields patterns with fewer 2s, which by induction already have count 1, forcing the third count to be 1 too. [ExactMarginals.lean](ExactMarginals.lean) proves this equivalence to `TBoards.Valid` for every board (see [exact-marginals-lean-build.log](exact-marginals-lean-build.log)).

You cannot drop the quadruple conditions completely. An explicit well-formed board has all **108** triple margins equal to 3, yet misses eight quadruples and doubles eight others; it even satisfies 15 of the 16 binary-cube conditions, doubling only `1111`. [MarginalCounterexample.lean](MarginalCounterexample.lean) checks this board in Lean's kernel ([marginal-counterexample-lean-build.log](marginal-counterexample-lean-build.log)), and a separate Cartesian audit checks its [recorded rows](experiments/exact_structure_counterexample.json).

```sh
lake build ExactMarginals MarginalCounterexample
```

The [reduced CNF generator](experiments/exact_reduced_cnf.py) encodes these same equations and passed all 16 encoding checks, while bounded unrestricted and prefix-C runs reached counting without finishing ([exact_reduced_notes.md](experiments/exact_reduced_notes.md)).

A second CNF model compares every pair of T placements directly using shared Boolean variables for equal-colored cell pairs. That shrinks the unrestricted normalized model to 5,382 variables and 50,363 clauses. All 27 exact-count checks passed, yet both bounded ternary runs timed out, including a prefix whose count is already known ([exact_compare_notes.md](experiments/exact_compare_notes.md)).

The [structural investigation](experiments/exact_structure.md) also rules out a direct BEST-theorem or determinant shortcut: local output permutations need extra cross-row compatibility conditions, so last-exit or boundary-sign data alone cannot decide acceptance.

## Exact geometric inclusion-exclusion

A [Möbius aggregation](experiments/exact_mobius_report.md) maps each collision of two T placements to four cell-equality equations. Grouping partitions that force the same cell equalities gives an exact polynomial `P_h(q)` counting height-`h` boards with distinct T patterns, where our target is `P_10(3)`. Two independent implementations agree through height 4 and match the board census.

Materializing the full closure table is infeasible: 17 disjoint T placements already generate a partition-lattice interval with 82,864,869,804 nonzero Möbius states. Symbolic summation can still handle that interval (its sum is `q^32 (q^4)_17`), but explicit examples show that component counts and size multisets throw away geometric structure needed for later collisions. The report records and verifies these exact limits without claiming an evaluated count.

## Exact parity characterization

There is also an exact parity condition. If all 81 patterns occur an odd number of times, every count is at least 1; since there are only 81 placements, every count must equal 1. Conversely, every valid board has all counts equal to 1, hence odd.

[ExactParity.lean](ExactParity.lean) proves `TBoards.ExactParity.valid_iff_odd` for `TBoards.Valid`, along with a saturation proof using mere presence of every pattern. A more general theorem, `valid_iff_congruent_one`, shows that every count being 1 modulo any integer $m > 1$ (prime or not) is equivalent to validity. The [build log](exact-parity-lean-build.log) confirms a clean kernel-checked build using only standard axioms.

```sh
lake build ExactParity
```

The [parity CNF implementation](experiments/exact_parity_notes.md) passes gate and small-count checks, while both full ternary variants and both prefix-C trials timed out. Because the installed counter rejects native XOR clauses, these runs only tested clause-encoded parity circuits and do not measure Gaussian or polynomial-algebra methods.

The [algebraic derivation](experiments/exact_parity_math.md) gives 80 Boolean moment equations of degree at most 4. Four whole-cell eliminations leave 192 Boolean variables while keeping all palette conditions on the eliminated cells. Exhausting all $2^{21}$ reduced binary assignments matches geometric checking everywhere and returns 168 solutions.

A Fourier change of variables gives a cleaner polynomial ideal: encode the three colors as the nonzero elements of `F4`, enforce `z_i^3 + 1 = 0`, and set 40 representative nonconstant Fourier moments to 0 (Frobenius gives the other 40). Every coefficient lies in `F2`, so we can work over `F2` directly. Four linear eliminations leave 96 variables and 136 generators.

The quotient dimension of this ideal equals the exact unrestricted labeled count: over `F4`, the squarefree domain quotient splits as a product of fields indexed by all ternary boards, and the moment equations pick out the valid boards; extending scalars from `F2` to `F4` preserves vector-space dimension. The [original ideal](experiments/exact_parity_math_fourier_original.sing) and [reduced export](experiments/exact_parity_math_fourier_reduced.json) passed checks on 322 valid boards and substitution checks, though their quotient dimension remains uncomputed. An [independent review](experiments/exact_parity_review_fourier.md) checked every reduced polynomial symbolically, verified the kept domain equations, and confirmed there is no hidden multiplicity or symmetry factor. The [Singular algebra backend](experiments/exact_algebra_backend_results.md) matched known nine-row fibers of size 1 and 6, and Singular's arbitrary-precision Hilbert calculation agreed with two independent monomial counters (including a fixture of dimension $10^{20}$). On the full reduced model, Singular hit its 2 GiB memory cap before finishing a standard basis, and its 90-second wall limit then expired with no count.

Completed bases are saved before Hilbert evaluation so a slow counting stage cannot lose a finished basis. The [independent monomial counter](experiments/exact_standard_monomials.md) uses big integers and requires an explicit completed-standard-basis attestation, rejecting leading terms of arbitrary generator lists.

The [prime-characteristic extension](experiments/exact_parity_math_prime.md) proves the same quotient-dimension identity for every prime `p = 2 mod 3`, using domains `z_i^3 - 1` and integer Fourier sums reduced mod `p`. At `p = 29`, the unary equations alone force exact color histograms; at `p = 5`, the triple layer already enforces exact triple margins (though stronger intermediate constraints do not guarantee faster basis computation). A [fresh geometric generator](experiments/exact_prime_fourier.py) builds these ideals directly without reusing characteristic-2 substitutions and can include all 80 nonconstant moments as redundant generators.

Adding all 80 moments helped on a fixed prefix: the six-completion nine-row fiber finished over `p = 29`, with Hilbert and both monomial counters returning 6. On the unrestricted 100-variable, 180-generator model (no fixed cells or symmetry breaking), both `std` and `slimgb` ran out of 2 GiB of memory without a basis. Two independent audits verified the inputs; see [exact_algebra_backend_prime_results.md](experiments/exact_algebra_backend_prime_results.md) for the breakdown between the completed fixed fiber and the failed full runs.

An [independent msolve F4 backend](experiments/exact_msolve_notes.md) uses prime-field linear algebra and the same two big-integer monomial counters. A small patch to its export path bypasses msolve's machine-integer staircase counter; exported bases match stock msolve on small inputs, including a $3^{100}$-dimension fixture and the six-completion board fiber. Two unrestricted `p = 29` trials timed out before exporting a basis, and a `p = 2` trial finished one degree-4 matrix before failing to allocate the next basis hash. None yielded an unrestricted count.

A reviewed support-only import patch avoids keeping unused matrix columns. An [audited variable permutation](experiments/exact_parity_math_pivot_audit.md) puts four dispersed linear pivots first, with no T touching more than one pivot. This keeps every equation, reproduces the six-completion fiber, and finishes one more degree-4 round on the full model before again hitting the 2 GiB limit with no basis ([exact_msolve_notes.md](experiments/exact_msolve_notes.md) records the hashes and terminal states). The backend also supports the 96-variable export with either 36 representative moments or all 72 nonzero substituted moments. An [independent actual-input audit](experiments/exact_parity_math_reduced_input_audit.md) rederives the substitution geometrically, checks that all four eliminated-cell cubic domains stay in place, and confirms the quotient dimension still equals the full unrestricted count. Further reviewed allocator changes pushed past that storage limit, then hit a null allocation in the next linear-algebra round (confirmed in debugger registers and disassembly). Dropping the pair-batch target to 1 avoided the crash in a 180-second run, which still timed out in degree 4 with no basis. A 3 GiB retry was blocked at startup by an available-memory check. None of these failed runs produced a count or proved zero.

A separate [signed-permutation study](experiments/exact_sign_math.md) rules out specific determinant shortcuts. Horizontal reflection flips the sign of the 81-pattern permutation, so the unrestricted signed sum is 0. Two certified canonical boards share their first nine rows and all 19 rotor-boundary colors yet carry opposite signs. A six-board identity rules out any factorized per-cell/color weights making all unrestricted signs positive or equal, and a 56-board XOR certificate rules out real factorized sign corrections even on canonical representatives. Both certificates pass independent sign and geometry checks. Other determinant or Pfaffian approaches remain open.

A [rotor scheduling audit](experiments/exact_rotor_abelian.md) rules out a direct abelian-network shortcut: for the same boundary and local permutations, swapping two ready updates can turn a valid completion into a capacity failure. Re-encoding permutations for any legal schedule (including deterministic adaptive schedules using only revealed data) still preserves the exact set size by bijection, without giving an evaluated total or speedup.

## Redundant elementary color-balance equations

The [elementary-symmetric audit](experiments/exact_parity_math_elementary.md) encodes exact unary color histograms as low-degree equations. In each T role, the 81 colors contain 27 copies of each nonzero `F4` element, giving the generating polynomial `(1 + t^3)^27`, whose quadratic elementary symmetric sum `e2` vanishes. One whole-role quadratic and three sparse boundary differences add four equations (plus their optional Frobenius partners).

Checking all 3,403 nonnegative color-count triples summing to 81 confirmed that `e1 = e2 = e4 = e8 = e16 = 0` forces `(27, 27, 27)`, while `e1 = e2 = 0` already forces every count to be 3 mod 4. The first augmentation adds only the four `e2` equations and their Frobenius partners, keeping ordinary squared variables. Because the cubic-domain quotient is radical, these redundant low-degree consequences leave the full Fourier ideal and its quotient dimension unchanged.

An [audited shift to cumulative-sum coordinates](experiments/exact_pivot_review_prefix_notes.md) shrinks these equations sharply. Order cells by their membership in the four roles and define `y_j = z_0 + ... + z_j`, with inverse `z_j = y_j + y_(j-1)`. The four unary sums drop to 1, 2, 4, and 5 terms, so eliminating four prefix variables leaves an isomorphic 96-variable quotient. The 100 transformed color cubics have 532 total terms, and the eight elementary quadratics have 616.

Since prefix variables can equal 0, the exporter keeps the transformed original color cubics instead of asserting `y_j^3 + 1 = 0`, while optional `y_j^4 + y_j = 0` equations follow directly from them. Independent checks rebuild every polynomial, test the inverse map, and verify all eight export modes. Appending a known nine-row prefix reproduces its 6 completions; the unrestricted run reaches degree 5 and then fails a checked monomial-storage allocation under a 3 GiB cap with no basis or count ([exact_msolve_notes.md](experiments/exact_msolve_notes.md)).

A [quartic augmentation](experiments/exact_pivot_math_prefix_e4.md) adds the `e4 = 0` layer using 14,194 terms and no extra variables: one whole-role quartic and three boundary differences, justified by explicit polynomial identities from the unary, quadratic, and cell-domain equations and checked by independent product expansion. Together, `e1`, `e2`, and `e4` force every role's color counts to be 3 mod 8. Neither `e8` nor `e16` has been added to the solver input.

## An exact model over the three-element field

The [natural F3 formulation](experiments/exact_f3_math.md) uses colors `0, 1, 2` directly with field equations `z^3 - z = 0`. Summing each nonzero monomial over `{0,1,2}^4` across all 81 placements gives target 0 for every exponent tuple except `(2,2,2,2)`, whose target is 1. Using the indicator `1 - (z - c)^2`, these 80 equations force every pattern count to be 1 mod 3; each count is therefore positive, and having only 81 placements forces all 81 counts to be 1.

[ExactNativeMoments.lean](ExactNativeMoments.lean) proves this exact equivalence to `TBoards.Valid` in Lean's kernel, using the 80 power sums over the geometric placements, the finite inverse transform, modular saturation, and the automatic constant moment, with only Lean's standard axioms. Computing the algebraic quotient dimension remains a separate computational problem.

```sh
lake build ExactNativeMoments
```

Over `F3`, linear coordinate changes preserve the field-domain ideal. Applying a signed cumulative-sum change of coordinates and four unary eliminations therefore leaves just 96 independent field cubics and 76 moment equations, with no substituted pivot domains or scalar-extension factors. Its quotient dimension equals the exact labeled count. Independent geometric expansion checked all 172 generators, and a fixed-prefix run directly reproduced 6 completions over `F3`.

Four redundant [role-histogram cubics](experiments/exact_f3_math_e3.md) add only 574 terms and no extra variables; explicit identities derive them from validity and the existing unary quadratic moments. On the unrestricted `F3` model, msolve reached degree 5 and used temporary-storage compaction cleanly, then failed an exponent-table allocation under its 3 GiB cap with no completed basis or count ([exact_f3_terminal_review_results.json](experiments/exact_f3_terminal_review_results.json)).

An [exact translation factorization](experiments/exact_f3_translation.md) separates the global color shift, leaving 95 coupled coordinates plus one independent apex variable `a` satisfying `a^3 - a = 0`. Triangular binomial identities prove the ideals before and after the change are equal. Because `a` stays in the exported ring, the quotient dimension still equals the full labeled count with all three shifts included (no external factor of 3). This model reproduced the six-completion prefix (with the apex value fixing `a`), then timed out after 300 seconds on the unrestricted run with no basis or count and no allocator error under the smaller-growth allocator.

An [independently checked variable permutation](experiments/exact_f3_order.md) keeps every equation and the independent offset factor while improving a monomial-cooccurrence heuristic. The full polynomial-support graph stays complete, so this reordering offers no decomposition or runtime guarantee.

We also ran the native-`F3` model through [Singular's two standard-basis algorithms](experiments/exact_native_singular.md). Both reproduced the six-completion prefix first, then ran out of 3 GiB of memory on the unrestricted model (`slimgb` after about 42 seconds, `std` after about 67 seconds) with no basis or count.

A narrowly scoped [checked byte-exponent build](experiments/exact_msolve_byte_review_notes.md) halves exponent-vector memory for these `F3` models while keeping ordinary arithmetic and catching any overflow before narrowing. Basis comparisons, finite-field checks, and sanitizer boundary tests all passed; it reduces memory use without yet completing the full count.

An [exact sign factorization](experiments/exact_f3_sign.md) picks one normalized board per global-negation pair via a 180-term degree-5 equation with a nonzero target. Together with the three-valued shift, an independent two-valued sign recovers every board uniquely; keeping both variables in the 97-variable ring leaves the quotient dimension equal to the full labeled count. A fixed-prefix run reproduced 6 completions under this bilinear color reconstruction, while an unrestricted 4 GiB run crashed with a segmentation fault in degree 5 from an unconfirmed cause, producing no basis or count ([exact_msolve_notes.md](experiments/exact_msolve_notes.md)).

An alternative [four-branch partition](experiments/exact_f3_sign_branches.md) uses only linear equations to pick the first nonzero difference between two distinct patterns. Every valid board lands in one branch, and both shift and sign factors stay inside each branch quotient, so the unrestricted count is the sum of all four completed branch dimensions. Different variable orders of the same branch are alternatives and must not be summed together, and any unfinished branch stays unknown rather than zero. Solver fixtures reproduced branch dimensions `6, 0, 0, 0` on the known nine-row prefix (with both integer counters agreeing), while the four unrestricted branches remain uncomputed.

An [affine elimination](experiments/exact_f3_branch_elimination.md) eliminates the solved branch coordinates, leaving 96, 95, 94, and 93 variables. Explicit identities preserve every field domain, and substitution checks cover all moment and histogram equations. These four reduced models obey the same sum rule and also reproduce the known-prefix dimensions `6, 0, 0, 0`.

A separate full-label Boolean encoding of branch 3 adds 21 direct equality/inequality clauses to the parsimonious CNF, verified by an exhaustive 2,187-assignment check. A 60-second deterministic GANAK run timed out without a count or satisfiability answer (`experiments/exact_f3_branch3_ganak.*`).

## The remaining obstacle

Finding the unrestricted total requires counting extensions of **every** admissible prefix or replacing that search with an evaluated exact formula. Adding more witnesses, finishing selected prefixes, or counting locally valid caps cannot settle the full count on its own. No unrestricted ternary computation here has finished.

A literature check also reviewed Condon, Dugan, Goldman, and Williams, [Polyomino Density](https://arxiv.org/html/2608.29231v1) (August 2026). That paper studies minimum uncolored board sizes and colored constructions; it gives no counting formula for these ternary boards.
