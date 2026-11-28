# Investigation of the exact ternary count

How many valid labeled three-color T boards exist in total? Let $N$ denote the exact unrestricted count of 3-colorings of the 100-cell ziggurat $Z_9$ in which all $3^4 = 81$ ordered upright T patterns occur once. The tightest verified bracket currently proved here is:

$$
45{,}083{,}592 \le N \le 1{,}185{,}818{,}059{,}470{,}602{,}086{,}065{,}654{,}202{,}368.
$$

See the [lower-bound certificate](SplicePalCertificates.lean), the [four-row upper-bound census](experiments/exact_rotor_upper_results.json), and the [independent upper-bound audit](experiments/exact_rotor_upper_review_results.json).

Finding $N$ exactly has turned out to be surprisingly hard, yet investigating it produced several clean, kernel-verified structural theorems and mapped out the exact computational barriers across combinatorics, SAT model counting, inclusion-exclusion, and polynomial algebra. This report documents every proved theorem and every exact counting method we built and tested.

## 1. A global symmetry theorem and structural rigidity

### Every valid board has an orbit of size 12

Every valid ternary board — not just the millions of boards in our splicing certificates — has **exactly 12 distinct images** under the 6 color permutations and horizontal reflection. In particular, $N$ is guaranteed to be a multiple of 12.

**The proof in one paragraph.** Because a board is valid, reading its 81 T windows defines a **bijection** between the 81 geometric placements and the 81 color patterns. Suppose some symmetry (a color permutation, optionally combined with horizontal reflection) fixed the board. Then it would have to map fixed placements bijectively to fixed patterns — so the count of fixed placements must equal the count of fixed patterns!

* **Without reflection:** no cells move, so all **81** placements are fixed. On patterns, however, only the identity fixes all 81 patterns (a color swap fixes 1 pattern; a 3-cycle fixes 0).
* **With horizontal reflection:** reflection fixes exactly the **9** center-column placements (one per lower row $r = 1, \ldots, 9$). How many patterns $(t, l, m, r)$ satisfy $(\pi(t), \pi(r), \pi(m), \pi(l)) = (t, l, m, r)$ for a color permutation $\pi$?
  * If $\pi = \text{id}$: $t, m$ are arbitrary and $l = r$, giving $3 \times 3 \times 3 = \mathbf{27}$ fixed patterns.
  * If $\pi$ is a transposition: $t, m$ must equal the single fixed color and $r = \pi(l)$ is forced by $l$, giving $1 \times 1 \times 3 = \mathbf{3}$ fixed patterns.
  * If $\pi$ is a 3-cycle: no color is fixed by $\pi$, giving **0** fixed patterns.

Since $9 \notin \{27, 3, 0\}$, no recolored reflection can fix a valid board either. Thus the stabilizer is always trivial, and composing/inverting the 12 symmetries produces 12 distinct valid boards.

**Lean formalization.** [ExactSymmetry.lean](ExactSymmetry.lean) proves `TBoards.ExactSymmetry.stabilizer_trivial` inside Lean's kernel from `Valid b` alone, with no assumptions on the cap, pivot, or provenance. From the same hypothesis, [ExactOrbit.lean](ExactOrbit.lean) proves:

* `TBoards.ExactOrbit.twelve_distinct_images`: the list `orbit b` has length 12, contains no duplicates, and consists entirely of valid boards.
* `TBoards.ExactOrbit.length_eq_twelve_mul_canonical`: any duplicate-free list of valid boards closed under all 12 symmetries has length 12 times the sublist picked by any selector choosing one canonical image per orbit. (The list of all valid boards satisfies these hypotheses, though Lean does not formalize whether a given solver's canonical-form clauses define such a selector or match `Valid`.)

```sh
lake build ExactSymmetry ExactOrbit
```

The build logs for the [stabilizer theorem](exact-symmetry-lean-build.log) and the [twelve-image corollary and counting step](exact-orbit-lean-build.log) confirm clean builds using only `propext`, `Classical.choice`, and `Quot.sound`.

### No larger static symmetry group

Can we enlarge this 12-element symmetry group by applying fixed *independent* color permutations at different cells (a cellwise "gauge transformation")? A separate [finite-rank argument](experiments/exact_structure_gauge.md) proves the answer is **no**: if a cellwise recoloring preserves all valid boards, all 100 cell permutations must be equal. Just 322 explicit valid boards force this via 160 XOR identities and an independently checked rank-161 certificate (not formalized in Lean).

That same note shows that the only cell permutations preserving the uncolored T-incidence structure are the identity and horizontal reflection. Combined with fixed cellwise recolorings, these give precisely the known 12 symmetries. (This still leaves open board-dependent maps or spatial permutations that preserve valid boards without preserving T-incidence.)

### Partitioning the exact count by top rows

An [exhaustive symmetry split](experiments/exact_parity_math_symmetry.md) expresses $N$ either as $3$ times the apex-zero count or as a weighted sum over **ten top-two-row fibers** whose orbit weights sum to $81$ (not uniformly 12, because small partial prefixes can be symmetric!). The [manifest and strict aggregation audit](experiments/exact_symmetry_split_notes.md) reproduce the binary count of 168 and refuse to report a ternary total until every fiber has an audited complete count. Global cubic homogeneity only recovers the apex factor of 3; a characteristic-29 apex-zero algebra run hit its 2 GiB memory cap before finishing a basis or count.

The [msolve cap auditor](experiments/exact_msolve_cap_split_notes.md) supports the same ten-case sum with explicit coefficient-extension divisors and input/basis provenance checks. Its geometry audit verified all ten models in characteristics 2 and 29; however, the first four-cell case (`0000`) timed out after 180 seconds with no basis, so no cap counts have finished yet.

## 2. Combinatorial algorithms, rotors, and model counting

We tested a wide spectrum of exact combinatorial search, dynamic programming, and SAT model-counting techniques — checking every implementation against the known exact binary board total (**168** labeled boards, **42** orbits) and known ternary prefix fibers.

### Frontier dynamic programming and the five-row cap census

* **Row-transfer DP:** The [row-transfer census](experiments/exact_algo_frontier.cpp) merges top prefixes that share the same last row and used-pattern set. With the apex fixed to `0`, there are **9,391,598** valid four-row prefixes and **9,379,134** distinct transfer states. Merging removes only about **0.13%** of states at this depth, so plain state-table DP does not compress enough for a full count.
* **Streaming counter and five-row census:** The [streaming counter](experiments/exact_algo_count.cpp) traverses deterministic prefix intervals, marks each run `COMPLETE` or `INCOMPLETE`, and discards partial counts from unfinished intervals so completed intervals add safely without ever confusing a timeout for an exact count. The [cap census wrapper](experiments/exact_algo_census.py) groups prefixes into explicit symmetry orbits and weights each by its true orbit size (since partial caps can have nontrivial stabilizers, blindly multiplying by 12 would overcount).
* That census exhausted all **1,572** three-row prefix orbits in about 189 seconds and proved there are exactly **198,649,032,096 five-row caps** covering 16 distinct T patterns. (These are 25-cell partial boards and may not extend to full 100-cell boards.) Every prefix, orbit size, and completion count is saved in [exact_algo_census_results.json](experiments/exact_algo_census_results.json), and the [counter report](experiments/exact_algo_results.md) details the scope, orbit weights, and independent checks:

```sh
python experiments/exact_algo_census.py --seconds 300
```

### Local output permutations ("rotors") and the analytic upper bound

An independent enumeration using [local output permutations](experiments/exact_math_rotors.py) reproduced all 168 binary boards and matched the cell-by-cell enumerator board for board. The idea is simple: each of the $3^3 = 27$ bottom triples $(l, m, r)$ must appear three times on a valid board — once beneath each top color `0`, `1`, `2`. Recording the 19 colors along a boundary together with the local permutation of `{0, 1, 2}` in which each of the 27 triples emits its top colors uniquely determines the entire board, subject to a deterministic acceptance test. This immediately yields the clean analytic upper bound:

```text
3^19 × 6^27 = 1,189,563,417,824,350,846,613,100,429,312.
```

Many parameter tuples fail the acceptance test, so this lies far above the true count (and refining the first four rows trims it slightly to the $1.1858 \times 10^{30}$ upper bound quoted at the top), yet it proves that 128-bit counters in the streaming solver can never overflow (see [exact_math.md](experiments/exact_math.md)).

Another exact pruning experiment requires the directed graph of unused patterns to decompose into trails matching the remaining row lengths. It reproduced the complete prefix counts of 138 and 36, but did not consistently outperform the baseline search in CPU time; it remains in [exact_math_search.cpp](experiments/exact_math_search.cpp), leaving the main solver untouched.

### SAT/CNF model counting and additional search backends

* **Parsimonious CNF encoding:** The [CNF model](experiments/exact_count_cnf.py) preserves exact counts — cell variables specify the board and all auxiliary variables are uniquely forced. Deterministic model counting reproduced the binary total of **168** and the **2** completions of a published seven-row ternary prefix. Full symmetry breaking selects **42** binary orbits and was checked on all 17,160 images of the earlier 1,430 ternary representatives; with `--orbit-canonical`, the ternary count multiplies by 12. Three bounded ternary runs timed out without a count: a six-row prefix (60 s), an unrestricted run with color breaking (120 s), and an unrestricted run with full symmetry breaking (60 s). See [exact_count_notes.md](experiments/exact_count_notes.md) for the encoding, commands, and solver details.
* **Phase-flip startup fix:** In the full-symmetry CNF model, the solver initially stalled searching for a *first* solution before counting even started (a bottleneck the earlier palette-only model had not hit). Applying a bijective Boolean variable flip maps a known valid board to the all-false assignment without altering the solution count, allowing full-symmetry runs to enter the counting phase ([exact_phase_notes.md](experiments/exact_phase_notes.md)). Even then, a 600-second baseline run timed out without a count, recorded with its input hash in [exact_phase_run.json](experiments/exact_phase_run.json).
* **Preprocessing and independent d4 backend:** Three further [preprocessing configurations](experiments/exact_config_notes.md) preserve the binary orbit count of 42; two recover the prefix-C count of 2, and one shrinks the unrestricted formula to 9,802 variables before counting, yet none finished the unrestricted ternary count within its time limit. (Tree decomposition could not run because the full formulas exceed this solver build's graph-size limit.) The independent [d4 backend](experiments/exact_backend_notes.md) uses GMP big integers and reproduces the raw binary count 168, orbit count 42, and prefix-C count 2; both full ternary runs entered counting and hit their 120-second limits without a total. Early decision logs show no component splitting, though the logs do not pinpoint the final bottleneck.
* **Alternative backtracking and DP strategies:**
  * An [adaptive colored exact-cover solver](experiments/exact_cover_results.md) (with cell propagation, matching filters, and independent-component multiplication) reproduces known exact counts and reduces search nodes on several prefixes, while unrestricted bounded runs still time out.
  * [Stronger marginal CNFs](experiments/exact_marginal_notes.md) preserve exact counts without yielding a net speedup.
  * An independent [bottom-up diagonal counter](experiments/exact_diagonal_results.md) matches binary and prefix counts yet cannot exhaust the unrestricted ternary board.
  * An [exact last-row dynamic program](experiments/exact_lastrow_results.md) merges identical bottom-row subproblems across upper boards and passes all 65,536 binary four-row prefixes plus 31 ternary nine-row prefixes. However, in the exhausted 138-board fiber, last-row work consumes only 0.19% of CPU time, so caching sees little reuse and adds overhead; the bottleneck in that search sits in earlier rows (though other algorithms might behave differently).
  * An [interleaved two-row recurrence](experiments/exact_tworow_results.md) pairs the bottom two rows together so bottom-row constraints prune earlier. It passes every binary three-row prefix, 84 ternary symmetry images, and both complete C/P prefix fibers, while its six-row integration hit a 90-second limit; neither caching nor this ordering produced a general speedup.

## 3. An exact reduced system of pattern counts (marginals)

Rather than checking all 81 four-cell pattern counts directly, can we replace most of them with simpler three-cell **marginal** counts? Yes — up to a sharp, kernel-verified threshold.

Write $N(a, b, c, d)$ for the number of times pattern $(a, b, c, d)$ appears on a board. Validity asks that all 81 counts equal 1. An **equivalent** system imposes:

1. **16 binary-cube equations:** $N(a, b, c, d) = 1$ for every $(a, b, c, d) \in \{0, 1\}^4$.
2. **65 selected three-coordinate margins equal to 3:** for the margin summing over coordinate $j \in \{0, 1, 2, 3\}$, keep only triples whose entries *before* $j$ lie in $\{0, 1\}$ — giving $27 + 18 + 12 + 8 = 65$ margins in all.

**Why this suffices (induction on the number of `2`s).** Take any pattern containing at least one `2`, and locate its *first* coordinate $j$ equal to `2`. Every entry before $j$ lies in $\{0, 1\}$, so the selected margin dropping coordinate $j$ is in our system and sums three pattern counts to 3. Replacing coordinate $j$ by `0` or `1` produces two patterns with strictly fewer `2`s, which by induction already have count 1 — forcing the third count to equal $3 - 1 - 1 = 1$ as well!

[ExactMarginals.lean](ExactMarginals.lean) proves this exact equivalence to `TBoards.Valid` for every board (see [exact-marginals-lean-build.log](exact-marginals-lean-build.log)).

**Why the binary-cube conditions cannot be dropped.** You cannot characterize validity using triple margins alone. An explicit well-formed board has **all 108** triple margins equal to 3, yet misses eight quadruples and doubles eight others — in fact, it satisfies 15 of the 16 binary-cube conditions, doubling only `1111`! [MarginalCounterexample.lean](MarginalCounterexample.lean) verifies this counterexample inside Lean's kernel ([marginal-counterexample-lean-build.log](marginal-counterexample-lean-build.log)), and a separate Cartesian audit checks its [recorded rows](experiments/exact_structure_counterexample.json).

```sh
lake build ExactMarginals MarginalCounterexample
```

**Solver experiments on reduced encodings:**

* The [reduced CNF generator](experiments/exact_reduced_cnf.py) encodes these exact 16 + 65 equations and passed all 16 encoding checks, while bounded unrestricted and prefix-C runs reached counting without finishing ([exact_reduced_notes.md](experiments/exact_reduced_notes.md)).
* A second CNF model compares every pair of T placements directly using shared Boolean variables for equal-colored cell pairs. That shrinks the unrestricted normalized model to 5,382 variables and 50,363 clauses; all 27 exact-count checks passed, yet both bounded ternary runs timed out, including a prefix whose count is already known ([exact_compare_notes.md](experiments/exact_compare_notes.md)).
* The [structural investigation](experiments/exact_structure.md) also rules out a direct BEST-theorem or determinant shortcut: local output permutations require extra cross-row compatibility conditions, so last-exit or boundary-sign data alone cannot decide acceptance.

## 4. Exact geometric inclusion-exclusion (Möbius aggregation)

Just as the chromatic polynomial counts proper $q$-colorings of a graph via inclusion-exclusion over edge collisions, we can ask for the exact polynomial $P_h(q)$ counting $q$-colorings of the height-$h$ ziggurat with **all T patterns distinct** — our target is $P_{10}(3)$.

A [Möbius aggregation](experiments/exact_mobius_report.md) maps each collision of two T placements to four cell-equality equations and groups partitions that induce the same cell equalities. Two independent implementations agree through height 4 and match the board census.

Materializing the full closure table, however, is infeasible: just **17 disjoint T placements** already generate a partition-lattice interval with **82,864,869,804** nonzero Möbius states. Symbolic summation handles that interval cleanly — its sum is $q^{32}(q^4)_{17}$ — but explicit examples show that tracking only component counts and size multisets discards geometric structure required for later collisions. The report records and verifies these exact limits without claiming an evaluated count.

## 5. Exact parity and Fourier polynomial ideals

### Validity is equivalent to a parity (or modular) condition

Here is a remarkably clean algebraic reformulation: **a board is valid if and only if every one of the 81 patterns occurs an odd number of times.** Why? If every count is odd, every count is at least 1; since the 81 counts sum to only 81 placements, every count is forced to equal 1! The exact same saturation trick works modulo *any* integer $m > 1$ (prime or composite): every count being $\equiv 1 \pmod m$ forces every count to be $\ge 1$, hence equal to 1.

[ExactParity.lean](ExactParity.lean) proves `TBoards.ExactParity.valid_iff_odd` for `TBoards.Valid`, along with a saturation proof using mere presence of every pattern, and the general theorem `valid_iff_congruent_one` for arbitrary $m > 1$. The [build log](exact-parity-lean-build.log) confirms a clean kernel-checked build using only standard axioms:

```sh
lake build ExactParity
```

The [parity CNF implementation](experiments/exact_parity_notes.md) passes gate and small-count checks, while both full ternary variants and both prefix-C trials timed out. Because the installed counter rejects native XOR clauses, these runs only tested clause-encoded parity circuits and do not measure Gaussian or polynomial-algebra methods.

### Turning counting into quotient-ring dimension

Modular characterizations translate validity into a system of polynomial equations $I$ over a finite field $\mathbb{F}$. When the domain equations force the quotient ring $\mathbb{F}[z_1, \ldots, z_n]/I$ to be **radical** (squarefree, with no repeated roots), the quotient splits over an appropriate field extension as one copy of the field per valid board — so the **vector-space dimension** of $\mathbb{F}[z]/I$ (read straight off the leading monomials of a Gröbner/standard basis) equals the **exact unrestricted count $N$**!

We built, audited, and benchmarked several progressively cleaner polynomial ideals:

* **Boolean moment equations:** The [algebraic derivation](experiments/exact_parity_math.md) produces 80 Boolean moment equations of degree at most 4. Four whole-cell eliminations leave 192 Boolean variables while preserving all palette conditions on the eliminated cells. Exhausting all $2^{21}$ reduced binary assignments matches geometric checking everywhere and returns 168 solutions.
* **Characteristic-2 Fourier ideal ($\mathbb{F}_4 / \mathbb{F}_2$):** Encode the three colors as the three nonzero elements of $\mathbb{F}_4$ via domain equations $z_i^3 + 1 = 0$, and set 40 representative nonconstant Fourier moments to 0 (the Frobenius map automatically supplies the other 40). Because every coefficient lies in $\mathbb{F}_2$, we can work directly over $\mathbb{F}_2$; four linear eliminations leave **96 variables and 136 generators**.
  * Over $\mathbb{F}_4$, the squarefree domain quotient splits as a product of fields indexed by all $3^{100}$ ternary boards, and the moment equations pick out precisely the valid boards; scalar extension from $\mathbb{F}_2$ to $\mathbb{F}_4$ preserves vector-space dimension, so the quotient dimension equals $N$ with no hidden multiplicity or symmetry factor.
  * The [original ideal](experiments/exact_parity_math_fourier_original.sing) and [reduced export](experiments/exact_parity_math_fourier_reduced.json) passed checks on 322 valid boards and substitution checks, and an [independent review](experiments/exact_parity_review_fourier.md) verified every reduced polynomial symbolically and checked the kept domain equations.
  * The [Singular algebra backend](experiments/exact_algebra_backend_results.md) matched known nine-row fibers of size 1 and 6, and Singular's arbitrary-precision Hilbert calculation agreed with two independent monomial counters (including a fixture of dimension $10^{20}$). On the full reduced model, Singular hit its 2 GiB memory cap before completing a standard basis, and its 90-second wall limit expired with no count.
  * Completed bases are always saved before Hilbert evaluation so a slow counting stage cannot lose a finished basis. The [independent monomial counter](experiments/exact_standard_monomials.md) uses big integers and requires an explicit completed-standard-basis attestation, rejecting leading terms of arbitrary generator lists.
* **Prime-characteristic extension ($p \equiv 2 \pmod 3$):** The [prime-characteristic extension](experiments/exact_parity_math_prime.md) proves the exact same quotient-dimension identity for every prime $p \equiv 2 \pmod 3$, using domains $z_i^3 - 1$ and integer Fourier sums reduced mod $p$. At $p = 29$, the unary equations alone force exact color histograms; at $p = 5$, the triple layer already enforces exact triple margins (though stronger intermediate constraints do not guarantee faster basis computation). A [fresh geometric generator](experiments/exact_prime_fourier.py) constructs these ideals directly without reusing characteristic-2 substitutions and can include all 80 nonconstant moments as redundant generators.
  * Including all 80 moments helped on a fixed prefix: the six-completion nine-row fiber finished over $p = 29$, with Hilbert and both monomial counters returning 6. On the unrestricted 100-variable, 180-generator model (no fixed cells or symmetry breaking), both `std` and `slimgb` ran out of 2 GiB of memory without a basis. Two independent audits verified the inputs; see [exact_algebra_backend_prime_results.md](experiments/exact_algebra_backend_prime_results.md).
* **Independent msolve F4 backend and pivot ordering:** An [independent msolve F4 backend](experiments/exact_msolve_notes.md) uses prime-field linear algebra paired with the same two big-integer monomial counters. A small patch to its export path bypasses msolve's machine-integer staircase counter; exported bases match stock msolve on small inputs, including a $3^{100}$-dimension fixture and the six-completion board fiber. Two unrestricted $p = 29$ trials timed out before exporting a basis, and a $p = 2$ trial finished one degree-4 matrix before failing to allocate the next basis hash.
  * A reviewed support-only import patch avoids storing unused matrix columns. An [audited variable permutation](experiments/exact_parity_math_pivot_audit.md) places four dispersed linear pivots first, with no T touching more than one pivot. This preserves every equation, reproduces the six-completion fiber, and finishes one more degree-4 round on the full model before again hitting the 2 GiB cap with no basis ([exact_msolve_notes.md](experiments/exact_msolve_notes.md) records the hashes and terminal states).
  * The backend also supports the 96-variable export with either 36 representative moments or all 72 nonzero substituted moments. An [independent actual-input audit](experiments/exact_parity_math_reduced_input_audit.md) rederives the substitution geometrically, verifies all four eliminated-cell cubic domains remain intact, and confirms the quotient dimension still equals $N$. Further reviewed allocator changes pushed past that storage limit before hitting a null allocation in the next linear-algebra round (confirmed in debugger registers and disassembly). Dropping the pair-batch target to 1 avoided the crash in a 180-second run, which still timed out in degree 4 with no basis. A 3 GiB retry was blocked at startup by an available-memory check. None of these failed runs produced a count or proved zero.

### Ruling out determinant and abelian-network shortcuts

Two focused structural studies checked whether algebraic cancellations or commutativity might allow a shortcut:

* **Signed permutations and determinants:** A separate [signed-permutation study](experiments/exact_sign_math.md) rules out specific determinant shortcuts. Horizontal reflection flips the sign of the 81-pattern permutation, so the unrestricted signed sum is identically 0. Moreover, two certified canonical boards share their first nine rows and all 19 rotor-boundary colors yet carry opposite signs. A six-board identity rules out any factorized per-cell/color weights making all unrestricted signs positive or equal, and a 56-board XOR certificate rules out real factorized sign corrections even on canonical representatives. Both certificates pass independent sign and geometry checks. (Other determinant or Pfaffian approaches remain open.)
* **Rotor scheduling and abelian networks:** A [rotor scheduling audit](experiments/exact_rotor_abelian.md) rules out a direct abelian-network shortcut: for the same boundary and local permutations, swapping two ready updates can turn a valid completion into a capacity failure. Re-encoding permutations for any legal schedule (including deterministic adaptive schedules using only revealed data) still preserves the exact set size by bijection, without yielding an evaluated total or speedup.

## 6. Redundant elementary color-balance equations

Inside a Gröbner-basis run, low-degree global constraints can sometimes trigger early cancellations. In each of the four T roles (top, left, middle, right), the 81 placements on any valid board must contain exactly **27 copies** of each of the three nonzero elements of $\mathbb{F}_4$. That produces the generating polynomial $(1 + t^3)^{27}$, whose quadratic elementary symmetric sum $e_2$ vanishes identically.

* **Quadratic balance ($e_2 = 0$):** The [elementary-symmetric audit](experiments/exact_parity_math_elementary.md) adds one whole-role quadratic and three sparse boundary differences (four equations, plus their optional Frobenius partners). Checking all 3,403 nonnegative color-count triples summing to 81 confirmed that $e_1 = e_2 = e_4 = e_8 = e_{16} = 0$ forces $(27, 27, 27)$, while $e_1 = e_2 = 0$ already forces every count to be $3 \bmod 4$. The first augmentation adds only the four $e_2$ equations and their Frobenius partners, keeping ordinary squared variables. Because the cubic-domain quotient is radical, adding these redundant low-degree consequences leaves the ideal and its quotient dimension unchanged.
* **Cumulative-sum coordinates:** An [audited shift to cumulative-sum coordinates](experiments/exact_pivot_review_prefix_notes.md) compresses these equations dramatically. Order cells by their membership in the four roles and set $y_j = z_0 + \cdots + z_j$, with inverse $z_j = y_j + y_{j-1}$. The four unary sums collapse to just 1, 2, 4, and 5 terms, so eliminating four prefix variables leaves an isomorphic 96-variable quotient. The 100 transformed color cubics take only 532 terms total, and the eight elementary quadratics take 616. Because prefix variables can equal 0, the exporter keeps the transformed original color cubics instead of asserting $y_j^3 + 1 = 0$ (while optional $y_j^4 + y_j = 0$ equations follow directly from them). Independent checks rebuild every polynomial, test the inverse map, and verify all eight export modes. Appending a known nine-row prefix reproduces its 6 completions; the unrestricted run reaches degree 5 before failing a checked monomial-storage allocation under a 3 GiB cap with no basis or count ([exact_msolve_notes.md](experiments/exact_msolve_notes.md)).
* **Quartic balance ($e_4 = 0$):** A [quartic augmentation](experiments/exact_pivot_math_prefix_e4.md) adds the $e_4 = 0$ layer using 14,194 terms and no extra variables: one whole-role quartic and three boundary differences, justified by explicit polynomial identities from the unary, quadratic, and cell-domain equations and checked by independent product expansion. Together, $e_1, e_2, e_4$ force every role's color counts to be $3 \bmod 8$. Neither $e_8$ nor $e_{16}$ has been added to the solver input.

## 7. An exact model over the three-element field ($\mathbb{F}_3$)

Working directly over the three-element field $\mathbb{F}_3 = \{0, 1, 2\}$ eliminates both scalar extensions and transformed domain cubics — because colors `0, 1, 2` *are* the elements of $\mathbb{F}_3$ with field equations $z^3 - z = 0$, and **every linear change of coordinates over $\mathbb{F}_3$ automatically preserves the field-domain ideal**!

### Exact moment equivalence in Lean

The [natural $\mathbb{F}_3$ formulation](experiments/exact_f3_math.md) sums each nonzero monomial over $\{0, 1, 2\}^4$ across all 81 T placements: every exponent tuple sums to 0 over $\mathbb{F}_3$ *except* $(2, 2, 2, 2)$, whose target is 1. Expanding the finite-field indicator $1 - (z - c)^2$ shows that these 80 power-sum equations force every pattern count to be $\equiv 1 \pmod 3$; each count is therefore positive, and having only 81 placements forces all 81 counts to equal 1.

[ExactNativeMoments.lean](ExactNativeMoments.lean) proves this exact equivalence to `TBoards.Valid` inside Lean's kernel — using the 80 power sums over the geometric placements, the finite inverse transform, modular saturation, and the automatic constant moment — relying only on Lean's standard axioms. (Computing the algebraic quotient dimension remains a separate computational problem.)

```sh
lake build ExactNativeMoments
```

### Coordinate reductions, factorizations, and solver benchmarks over $\mathbb{F}_3$

* **Signed cumulative-sum model (96 variables, 172 generators):** Applying a signed cumulative-sum coordinate change and four unary eliminations over $\mathbb{F}_3$ leaves just **96 independent field cubics** and **76 moment equations**, with no substituted pivot domains and no scalar-extension factors. Its quotient dimension equals the exact labeled count $N$. Independent geometric expansion verified all 172 generators, and a fixed-prefix run directly reproduced 6 completions over $\mathbb{F}_3$.
* **Redundant role-histogram cubics ($e_3$):** Four redundant [role-histogram cubics](experiments/exact_f3_math_e3.md) add only 574 terms and no extra variables, derived via explicit identities from validity and the existing unary quadratic moments. On the unrestricted $\mathbb{F}_3$ model, msolve reached degree 5 and ran temporary-storage compaction cleanly before failing an exponent-table allocation under its 3 GiB cap with no completed basis or count ([exact_f3_terminal_review_results.json](experiments/exact_f3_terminal_review_results.json)).
* **Exact translation factorization:** An [exact translation factorization](experiments/exact_f3_translation.md) factors out global color shifts $c \mapsto c + a \pmod 3$, leaving 95 coupled coordinates plus one independent apex variable $a$ satisfying $a^3 - a = 0$. Triangular binomial identities prove the ideals before and after the change are equal. Because $a$ stays inside the exported ring, the quotient dimension still equals the full labeled count $N$ with all three shifts included (no external factor of 3). This model reproduced the six-completion prefix (with the apex value fixing $a$), then timed out after 300 seconds on the unrestricted run with no basis or count and no allocator error under the smaller-growth allocator.
* **Variable ordering, Singular, and byte exponents:**
  * An [independently checked variable permutation](experiments/exact_f3_order.md) keeps every equation and the independent offset factor while improving a monomial-cooccurrence heuristic; however, the full polynomial-support graph stays complete, so reordering offers no decomposition or runtime guarantee.
  * We also ran the native-$\mathbb{F}_3$ model through [Singular's two standard-basis algorithms](experiments/exact_native_singular.md). Both reproduced the six-completion prefix first, then ran out of 3 GiB of memory on the unrestricted model (`slimgb` after about 42 seconds, `std` after about 67 seconds) with no basis or count.
  * A narrowly scoped [checked byte-exponent build](experiments/exact_msolve_byte_review_notes.md) halves exponent-vector memory for these $\mathbb{F}_3$ models while keeping ordinary arithmetic and catching any overflow before narrowing. Basis comparisons, finite-field checks, and sanitizer boundary tests all passed; it cuts memory footprint without yet completing the full count.
* **Exact sign factorization and four-branch linear partition:**
  * An [exact sign factorization](experiments/exact_f3_sign.md) selects one normalized board per global-negation pair ($c \mapsto -c \pmod 3$) using a 180-term degree-5 equation with a nonzero target. Together with the three-valued shift, an independent two-valued sign recovers every board uniquely; keeping both variables in the 97-variable ring leaves the quotient dimension equal to $N$. A fixed-prefix run reproduced 6 completions under this bilinear color reconstruction, while an unrestricted 4 GiB run crashed with a segmentation fault in degree 5 from an unconfirmed cause, producing no basis or count ([exact_msolve_notes.md](experiments/exact_msolve_notes.md)).
  * An alternative [four-branch partition](experiments/exact_f3_sign_branches.md) uses *only linear equations* to pick the first nonzero difference between two distinct patterns. Every valid board lands in exactly one branch, and both shift and sign factors stay inside each branch quotient, so $N$ is the sum of all four completed branch dimensions. (Different variable orders of the same branch are alternatives and must not be summed together, and any unfinished branch remains unknown rather than zero.) Solver fixtures reproduced branch dimensions `6, 0, 0, 0` on the known nine-row prefix (with both integer counters agreeing), while the four unrestricted branches remain uncomputed.
  * An [affine elimination](experiments/exact_f3_branch_elimination.md) eliminates the solved branch coordinates, shrinking the four branches to **96, 95, 94, and 93 variables**. Explicit identities preserve every field domain, and substitution checks cover all moment and histogram equations. These four reduced models obey the same sum rule and reproduce the known-prefix dimensions `6, 0, 0, 0`.
  * A separate full-label Boolean encoding of branch 3 adds 21 direct equality/inequality clauses to the parsimonious CNF, verified by an exhaustive 2,187-assignment check. A 60-second deterministic GANAK run timed out without a count or satisfiability answer (`experiments/exact_f3_branch3_ganak.*`).

## 8. The remaining obstacle

Determining the exact unrestricted total $N$ requires either counting extensions of **every** admissible prefix or replacing search with an evaluated exact formula. Adding more witnesses, exhausting selected prefixes, or counting locally valid caps cannot settle $N$ by themselves, and no unrestricted ternary computation here has completed.

A literature check also reviewed Condon, Dugan, Goldman, and Williams, [Polyomino Density](https://arxiv.org/html/2608.29231v1) (August 2026). That paper studies minimum uncolored board sizes and colored constructions; it provides no counting formula for these ternary boards.
