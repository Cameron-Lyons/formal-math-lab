# Prior proofs, originality, and research status

First checked **22 November 2026** (America/Chicago; some retrievals carry 23 November UTC timestamps), with follow-up checks through **27 November 2026**. This audit compares local results against existing proofs and public formalizations.

Summary of the checked entries:

* **No earlier proof or model found in checked sources:** E1486 at order 15, unit fractions, seven-cycles, and T-tetromino boards (checked **22 November 2026**); E670 at order 10, the 17-element E1486 model, and E1486 at order 12 (checked **23 November 2026**); the 26-element E1486 model and E1486 at order 14 (checked **24 November 2026**); and Erdős #602 plus the variants of Erdős #211, #338, #344, #387, and #1066 in limited searches through **25 November 2026** (the #1066 disproof is a short corollary of D. de Caen's 2000 theorem).
* **Formalizations or independent proofs of earlier results:** $\gamma(Q_{48}) = 25$ was published and certified by Aleksej Đukić on **22 November 2026** (which together with Östergård and Weakley's 2001 independent 25-queen set also implied $i(Q_{48}) = 25$); the three-column matrix formula follows from an earlier inclusion-exclusion theorem; the A026019 recurrence follows from Georg Fischer's first-order jOEIS recurrence (6 November 2026) and was also verified by Robert Israel on OEIS on 24 November 2026; the A176755 recurrence is covered by Georg Fischer (January 2020) and Artūras Dubickas (June 2026); E677 at order 10 formalizes José Brox's January 2025 report (no earlier Lean proof found on **24 November 2026**); and Erdős #708 formalizes C. Bergström's proved value $g(6) = 8$, importing John Tripodo's Lean bounds for four and five integers.
* **Open partial work:** E17260 gives partial obstructions, and finite nontrivial existence remained open in sources checked on **23 November 2026**.

None of these searches can prove that no earlier or unpublished result exists.

## Erdős #475, all sizes modulo 43 and four omitted residues at every prime

Checked **27 November 2026**. Arévalo reports complete finite verification through prime 37. Costa, Della Fiore, Fontana and Vena prove sequenceability through size 20 and through size 22 for zero-sum sets. The computation here independently covers every size at 43. Pham and Sauermann, together with earlier results, cover all sufficiently large primes. [Arévalo's computations](https://fabianarevalo.com/graham-rearrangement) · [Costa et al.](https://arxiv.org/abs/2603.20961) · [Pham and Sauermann](https://arxiv.org/abs/2602.15797) · [Modulo-43 proof](erdos-475-mod41-size27/modulo-43.md)

The four-omission construction extends the opposite-pair folding argument. Padding a triple with zero gives the same ordering rule for three or four unpaired residues of sum zero together with any collection of opposite pairs. This proves Graham's conclusion at size $p-5$ for every prime $p\ge5$. [Earlier folded cycle and attribution](erdos-475-mod41-size27/paired-triple.md) · [Four-omission proof](erdos-475-mod41-size27/paired-quartet.md)

## Erdős #475, all sizes modulo 41 and three omitted residues at every prime

Checked **27 November 2026**. Arévalo reports exhaustive checks for all primes through 37 and for sizes 28 through 40 at 41. The present search covers the entire prime 41, including the middle sizes. Pham and Sauermann, with earlier work, prove the conjecture for sufficiently large primes. Kuang and Wang treat sufficiently large subsets of finite abelian groups. These asymptotic results give no verified overlap with the finite range checked here. [Arévalo, results R1 and R3](https://fabianarevalo.com/graham-rearrangement) · [Pham and Sauermann](https://arxiv.org/abs/2602.15797) · [Kuang and Wang](https://arxiv.org/abs/2610.34424) · [Modulo-41 proof](erdos-475-mod41-size27/README.md)

The folded cycle for complete inverse pairs comes from the construction in Alspach, Gavlas, Šajna and Verrall, Lemma 3.4. Hicks, Ollis and Schmitt prove Alspach’s stronger nonzero-total result at size $p-3$. The argument here inserts a normalized triple into a folded cycle and proves Graham’s conclusion at size $p-4$ for every prime $p\ge5$. Searches under partial sums, sequenceability, difference cycles, and omitted residues found no earlier full modulo-41 check or all-prime proof specifically at size $p-4$. Priority and independent expert review are unconfirmed. [Alspach et al. (2003)](https://doi.org/10.1016/S0097-3165(03)00098-0) · [Hicks, Ollis and Schmitt, Theorem 4.6](https://arxiv.org/abs/1809.02684) · [Three-element insertion proof](erdos-475-mod41-size27/paired-triple.md)

## Erdős #475, size 27 modulo 41

Checked **27 November 2026**. Graham's problem concerns nonzero residues and nonempty partial sums. Arévalo's result R3 reports 227,999,052 dilation classes for sizes 28 through 40 modulo 41. Pham and Sauermann, together with earlier results, settle the conjecture for sufficiently large primes. I found no earlier verification of the size-27 case modulo 41 in the sources checked. [Problem statement](https://www.erdosproblems.com/475) · [Arévalo, R3](https://fabianarevalo.com/graham-rearrangement) · [Pham and Sauermann](https://arxiv.org/abs/2602.15797)

The direct computation checks all sets of total 0 or 1 and also keeps every proper nonempty partial sum away from zero. An independent proof uses a fixed-cardinality zero-sum reduction. A related replacement argument occurs in the Atomicium draft. [Computations and proof](erdos-475-mod41-size27/) · [Earlier reduction](https://github.com/Atomicium-org/graham-rearrangement-certificates/blob/23cb1d03e718d0798ff79161bff516444e7ca335/paper/graham_rearrangement_candidate.tex#L3513-L3575)

## Three stacks in series

Checked **26 November 2026**. Vatter attributes Question 5.4 to Waton. In the November update, Vatter reports with Jay Pantone that every 16-card order sorts and that a 21-card order fails. Their MathFest slides give the permutation. [Vatter, Question 5.4 and update](https://arxiv.org/html/2602.16355v4) · [MathFest slides](https://vincevatter.com/talks/2026-mathfest-stacks/)

The Lean package independently verifies the published obstruction and all 21 single-card deletions. A separate exhaustive computation covers every 19-card deck. Lean checks the reduction to decks ending in 1 and the last 384 sorting schedules. The grouped coverage remains an explicit hypothesis of the formal 20-or-21 result. [Lean theorems and audit instructions](three-stacks/)

## Seven slabs tiling a cube

Checked **26 November 2026**. Erich Friedman asks which cubes can be tiled using one slab of each order from 1 to $n$. Vamshi Jandhyala’s October 2026 preprint gives the upper bound $s \le n(n+1)/2$ on cube side length in Proposition 6. Proposition 7 rules out $n=4,5,6$. The last sentence of §6 states that the $n=7$ search had not been run. [Friedman’s problem 6](https://erich-friedman.github.io/mathmagic/unsolved.html) · [December 2001 problem](https://erich-friedman.github.io/mathmagic/1201.html) · [Jandhyala, §6, page 6](https://raw.githubusercontent.com/jvvk/mathematics/c6fecab25b6f821a7185bfdaa68c89bfaf54e4c7/math-magic-problems/paper/paper.pdf#page=6)

The Lean theorem rules out $n=7$ for a closed cube of arbitrary real side length, allowing each slab its own orientation. [Formal proof](seven-slabs/SevenSlabs.lean) · [Independent placement search](seven-slabs/verify/placement_search.cpp)

## Erdős #272, arithmetic progression intersections on thirteen points

Checked **26 November 2026**. Szabó's construction gives $t(13)\ge 82$. In August 2025 Stijn Cambie reported computations through 14, assuming for $10\le n\le14$ that the extremal family contains a singleton. Yang's Theorem 1.1 gives the unrestricted values through $t(12)=69$, and Theorem 1.4 gives the exact maximum for families with a common element for every $n$. [Szabó (1999), §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf#page=21) · [Cambie's forum post](https://www.erdosproblems.com/forum/thread/272#post-150) · [Yang (2026), Theorems 1.1 and 1.4](https://arxiv.org/html/2607.23004v1#S1)

OEIS A401861 lists the unrestricted values through $n=12$. A search for the thirteen-point case and for exact bounds on well-intersecting families found no earlier unrestricted upper bound of 82. The local computer-assisted proof rules out 83 when the total intersection is empty, completing the case $n=13$. The general formula remains open. [OEIS A401861](https://oeis.org/A401861) · [Proof and verification](erdos-272-thirteen/)

## Erdős #272, fourteen points and seven-term progressions

Checked **27 November 2026**. Szabó's construction gives 95 on fourteen points. Cambie's computation at this order assumed a singleton, and Yang proved the exact bound for all families with a common point. The searches for an unrestricted fourteen-point result found no earlier upper bound of 95. The local upper bound follows from an exhaustive clique search over all nonempty subsets. [Cambie's discussion](https://www.erdosproblems.com/forum/thread/272#post-150) · [Yang, Theorems 1.1–1.4](https://arxiv.org/abs/2607.23004) · [Proof and replay](erdos-272-fourteen/)

Conjectures.io records a verified proof of Szabó's linear-error asymptotic. The local result gives the exact value at every $N$ under a restriction on the number of members containing seven-term progressions. Priority of this restricted theorem is unverified. The unrestricted exact formula remains open. [Linear-error result](https://conjectures.io/problems/erdos272-erdos-272-variants-szabo-strong) · [Restricted theorem](erdos-272-fourteen/rank.md)

## Breaking every rectangle in a five-row matchstick grid

Checked **26 November 2026**. Dreyer and Biedl introduced the minimum number of unit edges whose removal breaks all axis-aligned rectangular outlines in a grid. Niu and Tang gave upper and lower bounds differing by at most one edge for grids of height five. [Dreyer and Biedl, DIMACS Technical Report 97-53, §4 (1997)](https://archive.dimacs.rutgers.edu/TechnicalReports/abstracts/1997/97-53.html). [Niu and Tang (2026)](https://doi.org/10.1016/j.tcs.2026.116199).

For a grid of $5 \times n$ unit squares, the Lean theorem proves the minimum is $5$ for $n=1$ and $\lfloor(10n+4)/3\rfloor$ for every $n\ge2$. Historical priority of this exact formula is unverified. [Formal theorem](five-row-matchsticks/Matchsticks.lean).

## Queen domination on the 48 × 48 board

Checked **24 November 2026** and re-audited **26 November 2026**. Östergård and Weakley (2001) gave an explicit independent 25-queen dominating set ([pp. 10-11](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v8i1r29/pdf/)), bounding both $\gamma(Q_{48})$ and $i(Q_{48})$ to $\{24, 25\}$. Davies listed 48 as the next open even board in [§9 of his 21 November preprint](https://hexagonmath.org/pdf/2611.00830v1#page=19).

**Earlier public solution (22 November 2026):** Aleksej Đukić publicly proved and certified $\gamma(Q_{48}) = 25$ on **22 November 2026**, two days before `queen-domination-48` (24 November) and three days before `queen-domination-48-sat` (25 November). He posted `a(48) = 25` to [OEIS A075458](https://oeis.org/A075458) (revision 125) with a certificate summary ([a075458_1.txt](https://oeis.org/A075458/a075458_1.txt)) reporting that CaDiCaL and `drat-trim` refuted all 47,580 canonical cases of Davies' frame reduction, alongside his [GitLab repository](https://gitlab.com/aleksejdj2019/queen-domination-extension), [project paper](https://queen-domination-extension.vercel.app/paper.pdf) (dated 22 November 2026), and Zenodo preprint ([10.5281/zenodo.24537292](https://zenodo.org/records/24537292), deposited 25 November 2026).

Because $\gamma(Q_n) \le i(Q_n)$ holds universally and Östergård and Weakley's 25-queen placement is already independent, Đukić's proof of $\gamma(Q_{48}) = 25$ immediately implied $i(Q_{48}) = 25$ on 22 November 2026 (although neither Đukić nor [OEIS A075324](https://oeis.org/A075324) explicitly wrote out that corollary). Neither local project is therefore the first mathematical solution of $\gamma(Q_{48}) = 25$ or $i(Q_{48}) = 25$. Locally, [queen-domination-48](queen-domination-48/README.md) contributes an independent, non-SAT mod-3 grid-partition proof in compiled Lean, and [queen-domination-48-sat](queen-domination-48-sat/README.md) formalizes Davies' Layer-2 CNF-encoding soundness in Lean's kernel, replays the 47,580 LRAT certificates with a compiled Lean checker, and explicitly proves $i(Q_{48}) = 25$.

## Box-free colorings of the 5 × 8 grid

Checked **27 November 2026**. Genkin’s version 2 constructs 42 layers and gives the upper bound 46. Question 8.4 asks for the exact height. The three seeds in this project give 45 layers, verified both in Lean and with the paper’s supplementary checker. [Genkin, Lemma 2.1 and Theorem 5.1](https://doi.org/10.5281/zenodo.24457907) · [Construction and certificate](box-free-5x8/README.md)

## Box-free colorings of the 6 × 7 grid

Checked **24 November 2026**. Genkin's version 2 builds a box-free 6 × 7 × 50 coloring and proves 52 as the upper bound ([Genkin, Theorem 5.1 and Question 8.1](https://zenodo.org/records/24457907)). Question 8.1 asks whether 52 can be reached. This project gives an explicit 52-layer [coloring](box-free-6x7/BoxFree/Construction.lean) and a Lean [exact-height theorem](box-free-6x7/BoxFree.lean) proving 52 is the maximum.

## Two triples producing nine squares

Checked **24 November 2026**. Dujella asks the six-integer question as [Problem 1.4](https://web.math.pmf.unizg.hr/~duje/pdf/open2.pdf#page=2). Batta, Hajdu, and Pongrácz list the case of three vertices on each side as open ([§6](https://arxiv.org/html/2410.20120v1#S6)). The [Lean proof](square-triples/SquareTriples/Ratio.lean) rules out any solution where both triples span a factor of at most 1,000. Priority of this bound is unverified.

## Longest snakes on a 13 × n grid

Checked **26 November 2026**. Tong Niu proves the maximum area of a snake polyomino at each fixed height through 12 and identifies height 13 as a next computational case. OEIS A360917 tabulates longest induced paths in rectangular grids. The local C++ computation gives a formula for every width at height 13. [Niu, §8](https://arxiv.org/html/2611.26640v1#S8) · [OEIS A360917](https://oeis.org/A360917) · [Height-13 proof and verifiers](research/height-13-snakes/)

## Longest snakes on a 14 × n grid

Checked **26 November 2026**. The height-14 formula agrees at widths 1 through 16 with the rectangular grid data in OEIS A360917. Niu's fixed-height formulas cover heights through 12. At height 14, two local computations prove a gain of 52 squares every six columns from width 18 onward. [OEIS A360917 data](https://oeis.org/A360917/b360917.txt) · [Niu, §8](https://arxiv.org/html/2611.26640v1#S8) · [Height-14 proof and verifiers](research/height-14-snakes/)

## Nine-bit snake-in-the-box

Checked **24 November 2026**. Orland et al. published 131 inequivalent induced paths of 191 edges in the 9-dimensional cube, reported that none extends by one edge, and asked whether a 192-step path exists ([Orland et al., §8](https://arxiv.org/html/2607.15270v3#S8), [published records at the pinned revision](https://github.com/Math-AI-Caltech/Snake-in-the-Box/blob/46c765399353a588ea50444a5d6610f53102b1c2/record_snakes.csv.zip)). [Kunt, Koch, and Park](https://arxiv.org/abs/2611.25268) also note dimension 9 as the smallest open case.

The Lean project keeps the first 156 steps of each published path in both orientations. Its `native_decide` checks rule out any 192-step completion and place every 191-step completion in one of the 131 known classes. Kernel reduction also rules out 192 steps when the first 171 steps are kept. Another kernel proof shows that a 191-step path is outside every published class if the distances back to its starting endpoint after steps 1 through 17 match in both orientations. See [prefix exclusion](nine-bit-snake/Results.lean), [kernel check](nine-bit-snake/KernelChecks.lean), and [classification and endpoint test](nine-bit-snake/Closure.lean).

## Two squares of each side from 1 through 21

Checked **24 November 2026**. Friedman's [results table](https://erich-friedman.github.io/mathmagic/0505.html) bounds the minimum number of copies of each size needed to tile a rectangle between two and five. On 22 November he updated [open problem 10](https://erich-friedman.github.io/mathmagic/unsolved.html) and kept the two-copy case for `n = 21` open ([dated revision](https://github.com/erich-friedman/erich-friedman.github.io/commit/4072f4a7ec4aacba7590ddd5ccb016a922ea594c)).

Searches by dimensions, area, square inventory, and the three-squares-per-row argument found no earlier proof ruling out 43 × 154, though priority is unconfirmed. The Lean reduction leaves 77 × 86 open. See [width-43 proof](consecutive-squares-21/Width43.lean) and [reduction](consecutive-squares-21/Bridge.lean).

## Five 30-sided Go First Dice

Checked **24 November 2026**. The Go First Dice team lists as open whether five 30-sided dice labeled 1 through 150 can give all 120 rankings equal odds ([researchers' open question](http://gofirstdice.ericharshbarger.org/doku.php?id=open_questions#d30)). The [October preprint, §1.2](https://arxiv.org/html/2610.15421v1#S1.SS2) by Gavenčiak, Haeupler, and Rozhoň credits Paul Meyer with a five-die construction using 60 faces per die.

The team reports an exhaustive search ruling out every column-grouped labeling, where each block of five consecutive labels gives one face to each die ([researchers' solution counts](http://gofirstdice.ericharshbarger.org/doku.php?id=homogeneous_solutions#column_paired)). That already covers the fifteen mirrored permutation blocks ruled out here ([mirrored-block proof](five-30-sided-dice/MirroredObstruction.lean)). No earlier statement of the modulo-four condition was found, though its priority is unconfirmed ([modulo-four proof](five-30-sided-dice/EqualCuts.lean)).

## Three integer cubes summing to 114

Checked **23 November 2026**. [Booker and Sutherland, §5.2](https://arxiv.org/pdf/2007.01209#page=14) report a search for 114 using cube roots modulo the pair sum. [Grantham and Walsh](https://arxiv.org/abs/2211.12149) describe a related number-field search, and [Welsh, Theorem 3](https://arxiv.org/abs/2008.00538) gives the general correspondence between cubic ideals and pairs of roots. The [local proof](three-cubes-114/TernaryFamily.lean) gives an elementary family outside the absolute norms of $\mathbb Z[\sqrt[3]{114}]$. Historical priority is unverified.

## E677 implies E255 at order nine

Checked **23 November 2026**. On 10 December 2024, José Brox reported an exhaustive Mace4 search ruling out 9-element magmas that satisfy E677 and fail E255 ([Brox's search report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#487358914)). The [Lean proof](E677-E255-order-9/Nine.lean) independently checks this case with an LRAT certificate.

## E677 at order ten

**Audited statement:** no 10-element magma satisfies `x = y*(x*((y*x)*y))` universally. In particular, E677 implies E255 at order ten.

Checked **24 November 2026**. Both claims appeared earlier from searches that were not machine-checked. On [22 December 2024](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#490346469) José Brox reported that size 10 was ruled out for E677 magmas failing E255. On [12 January 2025](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#493229385) he wrote: "There are no models whatsoever of 677 in size 10 (39h in Mace4)." On 21 November 2025, [Rudi Schneider](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#558558838) reported that his search program enumerates all E677 magmas through size 11, and [Jihoon Hyun](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#558568783) reported that CaDiCaL gave a negative result for size 10 in about six hours (runs described elsewhere in that thread encode E677 with a failure of E255). The [ICARM database](https://eq677.icarm.cloud/size/10) lists no size-10 models and cites Brox's search and a six-hour CaDiCaL run.

Two later reports describe SAT refutations of the weaker statement with DRAT certificates checked by drat-trim: [Issue 1464](https://github.com/teorth/equational_theories/issues/1464) on the Equational Theories Project's main repository (22 July 2026) and a prove2.me [mission page](https://prove2.me/missions/Equational_Magmas%3A_E677_%E2%86%92_E255_(finite_case)). Neither publishes its certificates or gives a Lean proof.

No Lean proof of either statement was found in the main repository, in the fork `Timeroot/equational_theories`, in other public E677 repositories found by search, or in the public Equational channel of the Lean Zulip. The fork's live [spectrum data](https://ohaithe.re/equational_theories/research/data/spectrum.json), last modified **5 November 2026**, lists Lean exclusions for E677 at orders 2, 3, 4, 6, and 8 and leaves 10 as its smallest undecided order. Its [order-ten report](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/docs/order_ten_followup_20261007.md#what-remains-at-ten) records the E677 searches at ten as unfinished. This folder adds a Lean-checked proof of Brox's January 2025 report rather than a new mathematical result; first-formalization status is unverified. See [Lean proof](E677-E255-order-9/Ten.lean).

## E1486 at order 15

**Audited statement:** no 15-element magma satisfies `(y*x)*(x*(z*z)) = x` universally.

Both the [pinned research note](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/1486_graph_spectrum.md) and the [live spectrum data](https://ohaithe.re/equational_theories/research/data/spectrum.json) list 15 as unresolved for E1486. The live data response was last modified **5 November 2026** and lists `[12,14,15,17,26]` as unresolved for both E1486 and its dual E2126, with no pending proofs. A [filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json) saves the response hash and headers.

No earlier order-15 proof was found. The law, square-row identities, and earlier spectrum results belong to the Equational Theories Project; this folder claims only the order-15 nonexistence proof, not the full spectrum or the first formal study of E1486.

## E1486 at order 17

**Audited statement:** some 17-element magma satisfies `(y*x)*(x*(z*z)) = x` universally.

Checked **23 November 2026** (24 November UTC). The pinned research note and live spectrum data cited for order 15 also list 17 as unresolved. The live response has not changed since **5 November 2026** and matches the hash in the [filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json). The note's [search data](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/data/spectrum/1486_search_followup.json) record one attempt at order 17: a CaDiCaL run on the full law that hit its 60-second limit with result `UNKNOWN`.

That note, catalogue, and data live on a branch of a fork. The main project's [commentary](https://github.com/teorth/equational_theories/blob/02b063b67143a897f070803482691c820770501d/commentary/Equation1486.md) says only that the finite spectrum is unknown, and its [equation list](https://github.com/teorth/equational_theories/blob/02b063b67143a897f070803482691c820770501d/data/equations.txt#L1486) gives Equation 1486 as `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`, matching the law checked here.

No earlier 17-element model or order-17 exclusion was found in the fork, in the main repository's issues and pull requests, or in the public Equational channel of the Lean Zulip. The [earlier discussion](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Understanding.20Finite.201486.20Magmas.html) of sporadic models does not mention order 17. This folder claims only this model, not the full spectrum. See [Lean proof](E1486-order-15/Simple/Order17.lean).

## E1486 at order 12

**Audited statement:** no 12-element magma satisfies `(y*x)*(x*(z*z)) = x` universally.

Checked **23 November 2026** (24 November UTC). Order 12 is likewise listed as unresolved in the pinned note and the live spectrum data (unchanged since **5 November 2026**, matching the hash in the [filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json)). The note is unchanged at the fork's latest research revision, [`199f75c2`](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/docs/1486_graph_spectrum.md).

Earlier attempts at order 12 did not decide it. The note's [search data](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/data/spectrum/1486_search_followup.json) record three 60-second CaDiCaL runs (one unrestricted and two with a normalized row), all ending in `UNKNOWN`. A later [search campaign](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/docs/spectrum_search_campaign_20261011.md) ran four restricted cases for 900 seconds each; one returned `UNSAT` and three timed out, and its report says "No order-12 existence or nonexistence claim follows from this partial search." On 28 September 2026, Bruno Le Floch [reported](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Writing.20a.20paper.20on.20the.20spectrum.20of.20an.20equational.20law/near/627564683) on the Lean Zulip that he stopped a Mace4 search at size 12 after 14 hours.

No earlier order-12 exclusion or 12-element model was found in the fork, in the main repository's issues and pull requests, or in the public Equational channel of the Lean Zulip. This folder claims only this exclusion, not the full spectrum. See [Lean proof](E1486-order-15/Simple/Order12/NoTable.lean).

## E1486 at order 26

**Audited statement:** some 26-element magma satisfies `(y*x)*(x*(z*z)) = x` universally.

Checked **24 November 2026**. Order 26 is also listed as unresolved in the pinned note (unchanged at revision [`199f75c2`](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/docs/1486_graph_spectrum.md)) and the live spectrum data (unchanged since **5 November 2026**, matching the hash in the [filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json)).

Earlier attempts did not decide order 26. The note reports that a uniform two-fold lift of the known 13-element model is impossible and that a solver refuted three nonuniform alternatives, adding that these results "do not imply that every 26-element model is impossible." The note's [search data](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/data/spectrum/1486_search_followup.json) record one 60-second CaDiCaL run on the full law at order 26, which ended in `UNKNOWN`.

No earlier 26-element model or order-26 exclusion was found in the fork, in issues and pull requests of the fork or main repository, or by web search. The archived Zulip [discussion](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Understanding.20Finite.201486.20Magmas.html) of sporadic models does not mention order 26. This folder claims only this model, not the full spectrum. See [Lean proof](E1486-order-15/Simple/Order26.lean).

## E1486 at order 14

**Audited statement:** no 14-element magma satisfies `(y*x)*(x*(z*z)) = x` universally.

Checked **24 November 2026**. Order 14 is listed as unresolved in the pinned note (unchanged at revision `199f75c2`) and the live spectrum data (unchanged since **5 November 2026**, matching the hash in the [filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json)).

The note's [search data](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/data/spectrum/1486_search_followup.json) record one attempt at order 14: a 60-second CaDiCaL run on the full law that returned `UNKNOWN`. No earlier order-14 exclusion or 14-element model was found in the fork, in issues and pull requests of the fork or main repository, in the public Equational channel of the Lean Zulip, or by web search. See [Lean proof](E1486-order-15/Simple/Order14/NoTable.lean).

Orders 12, 14, 15, 17, and 26 are the five orders listed as unresolved for E1486 in the live spectrum data. That record marks two bounds from the fork's Lean development as proved: no model at orders 2, 3, 5, 6, 7, 8, and 10, and a model at every other positive order outside those five. Combined with the five results here, the orders with no model are exactly 2, 3, 5, 6, 7, 8, 10, 12, 14, and 15. This combined statement is not checked as a single theorem, and the fork's proofs were not re-verified here.

## E17260: partial results, finite existence unresolved

Checked **23 November 2026**. The law is `x = (y*x)*(z*(x*(z*z)))` for all `x,y,z`. The Lean theorems here show that a model has at most one element if it has an idempotent, surjective squaring, left or right cancellation, or an affine operation on a commutative additive monoid. They also rule out 2-cycles of the squaring map and prove finite counting bounds. **They do not settle finite nontrivial existence.** See the [project and theorem endpoints](E17260-partial-results/).

The Equational Theories Project's [catalogue at the inspected 23 November 2026 revision](https://github.com/teorth/equational_theories/blob/02b063b67143a897f070803482691c820770501d/blueprint/src/chapter/order_5.tex#L99-L110) still lists finite existence for E17260 and its dual E28740 as unknown. [*Trace-Tree Magmas*, arXiv v3, revised 22 September 2026](https://arxiv.org/html/2609.05690v3#S7.SS2) gives Lean-certified infinite models and explicitly leaves the finite question open in Table 4 and [Section 9](https://arxiv.org/html/2609.05690v3#S9). Those infinite models are prior work.

The 16 December 2024 Zulip discussion already reported [exhaustive exclusion through order 10](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Some.20results.20from.20order.205.html#489163277) and [absence of finite linear models, including noncommutative coefficients](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Some.20results.20from.20order.205.html#489207891). The local affine proof does not assume finiteness, but makes no novelty claim. Novelty and first-formalization status of the other partial obstructions are unverified. Local searches at orders 11-20 were inconclusive and do not improve the known order-10 bound.

## Integer cubic $z^2+y^2z+x^3=2$

Checked **24 November 2026**. Grechuk lists infinitude of integer triples as open in Table 6 ([Grechuk, §5](https://arxiv.org/html/2404.08518v11#S5)). Epoch gives polynomial families for related cubics ([Epoch's two constructions](https://epoch.ai/files/open-problems/small-diophantine-two-families.pdf)) and asks for three integer triples on this cubic with distinct $x$ and $|x| > 10^{50}$ ([Epoch's challenge](https://epoch.ai/frontiermath/open-problems/small-diophantine)).

This folder proves a degree bound for polynomial families through an integer triple and gives a family where $x, z$ are integers and $y$ has reduced denominator 13. Historical priority for these partial results is unverified. See [project proof and checker](integer-cubic/README.md).

Lean also proves that a rational quartic substitution on $u^2 - 3v^2 = 1$ with nonconstant $x$ and one integral seed yields infinitely many integer triples ([quartic theorem](integer-cubic/pell/MixedPellAmplification.lean)). Bounded coefficient searches found no such substitution in the classes tested ([search scope](integer-cubic/pell/QuarticFreeMark.md)). A separate Lean theorem rules out the quintic substitution $az = 2 - r^3$, $x = r - p^2z$ for nonzero rational $a$ when $r, p$ have simple poles at both conjugate ends of a nonsplit Pell conic and all coordinates are regular away from those ends ([quintic exclusion](integer-cubic/pell/QuinticSquareObstruction.lean)). Priority for these results is unverified.

## Reciprocal Rado numbers $f_2(k) = 3k^2$ for all even $k \ge 4$

Checked **26 November 2026**. For every even integer $k \ge 4$, [`EvenUnitFractions.forces_iff`](even-unit-fractions/EvenUnitFractions.lean) proves in pure Lean 4 stdlib (axioms `[propext, Classical.choice, Quot.sound]`, no `native_decide`) that every 2-coloring of $\{1, \ldots, N\}$ has a monochromatic solution to $1/x_1 + \cdots + 1/x_k = 1/y$ (with repetitions allowed) if and only if $N \ge 3k^2$.

[Gaiser and Ramezanpour, arXiv:2607.04373v1](https://arxiv.org/abs/2607.04373) (submitted 5 July 2026; 0 citations in OpenAlex on 26 November 2026) prove the lower bound $f_2(k) \ge 3k^2$ for all $k \ge 3$ (Theorem 1.1), compute $f_2(k)$ through $k = 25$, prove equality $f_2(k) = 3k^2$ for the family $k = 3 \cdot 2^m$ (Theorem 3.3), and conjecture $f_2(k) = 3k^2$ for every $k \ge 4$ that is not an odd prime power (Conjecture 1.3). Fabian Arevalo's [repository](https://github.com/farev/Matematica/blob/main/conjectures/reciprocal-rado/README.md) certifies values through $k = 8$ and states $f_2(k) = 3k^2$ for all even $k \ge 4$ as Conjecture B with an unproved mechanism sketch. OpenAlex and web searches on 26 November 2026 found no earlier proof covering all even $k \ge 4$. Odd composite non-prime-power values of $k$ remain open in general.

<a id="reciprocal-rado"></a>

## Reciprocal Rado number f₂(26) = 2028

**Audited statement:** every 2-coloring of `[1,N]` forces the 26-summand reciprocal equation, with repetitions allowed, exactly when `N ≥ 2028`.

[Gaiser and Ramezanpour, arXiv:2607.04373v1](https://arxiv.org/html/2607.04373v1) give the general lower bound and some identities used here. Their computed table stops at 25, and their proved family $k = 3 \cdot 2^m$ does not include 26. The [arXiv record](https://arxiv.org/abs/2607.04373) lists only v1, submitted 5 July 2026. No earlier proof of the exact 26-summand upper bound was found.

Earlier Lean work on this problem exists. Korea Superintelligence Labs' [Machina Mathematica](https://lean.up.railway.app/) lists certified reciprocal Rado values at smaller parameters and a general lower bound ([data](https://lean.up.railway.app/api/data)). Fabian Arevalo's [research note](https://fabianarevalo.com/reciprocal-rado) and [repository](https://github.com/farev/Matematica/blob/main/conjectures/reciprocal-rado/README.md) also cover smaller values; the general even-parameter mechanism there is a sketch rather than a proof covering 26. This collection does not claim the first Lean work on reciprocal Rado numbers.

## Reciprocal Rado number f₂(28) = 2352

Checked **26 November 2026**. Gaiser and Ramezanpour proved the lower bound $f_2(k)\ge 3k^2$ for $k\ge3$ and calculated the two-color values through $k=25$. Their Conjecture 1.3 predicts $2352$ at $k=28$. [Theorem 1.1 and Conjecture 1.3](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem1)

The six-sum upper bound here adapts the opening pair of identities from Case 1 of their Theorem 3.3. Arevalo's separate project certifies two-color values through $k=8$ and sketches an argument for even $k$. [Case 1](https://arxiv.org/html/2607.04373v1#S3.Thmtheorem3) · [Arevalo’s results](https://github.com/farev/Matematica/blob/main/conjectures/reciprocal-rado/README.md) · [28-term proof](28-unit-fractions/)

## Erdős #64, power-of-two cycles

Checked **25 November 2026**. Erdős and Gyárfás asked whether every nonempty finite simple graph with minimum degree at least 3 contains a cycle of power-of-two length ([Erdős Problem #64](https://www.erdosproblems.com/64)). The general conjecture is still open. [Ducoffe and Dumitru](https://arxiv.org/abs/2609.28594) checked every graph on at most 40 vertices.

Hegde, Sandeep, and Shashank proved the conjecture for $P_{13}$-free graphs and forced a 4- or 8-cycle in $P_{12}$-free graphs, while their parallel search ran out of memory at $P_{14}$ ([Hegde, Sandeep, and Shashank, Theorems 0.1-0.2 and Table 1](https://arxiv.org/html/2410.22842v2)). This repository first proved the case forbidding $P_{14}\sqcup K_1$, and now forces a cycle of length 4, 8, or 16 when the forbidden induced subgraph is $P_{15}\sqcup K_1$, or $P_{17}\sqcup K_1$ for triangle-free graphs ([local proofs and verification](erdos-64-power-of-two-cycles/README.md)). In both cases the forbidden subgraph means every induced path of that order dominates the graph. Priority for these exact statements is unverified.

Two other local results cover graphs of pathwidth at most 3 and abelian voltage covers of $K_4$. [Bachtler and Heinrich](https://arxiv.org/abs/2010.08373) studied unavoidable subgraphs of bounded-pathwidth graphs, including short cycles in cubic graphs. [Burkhart](https://arxiv.org/abs/2611.05060) proved the Erdős-Gyárfás conjecture for Cayley graphs of odd-order groups and finite nilpotent groups. Cinna Davis used a voltage and collision certificate to prove a sharp bound of 32 for abelian covers of $K_4$ with one edge subdivided ([Davis, proof for the subdivided tetrahedron](https://itsdavis.com/solved-conjectures/results/erdos-gyarfas-abelian-covers/proof/)). The voltage theorem here gives the sharp bound 16 for $K_4$ itself. Priority for both local results is unverified.

Lemma 2.1 of [Ducoffe and Dumitru](https://arxiv.org/html/2609.28594v1) gives an odd cycle through an edge of a minimal counterexample by contraction, and their §4.1 gives the one-deficient-vertex reduction. The vertex-identification theorem here also handles nonedges and pairs with a common neighbor of degree at least 4. [Garcia](https://arxiv.org/html/2609.04686v1) asks about minimum and maximum path lengths in a two-terminal cubic fragment (Proposition 6.2) and proves $f(6) \le 32{,}640$ (Theorem 5.1). Here, Lean proves terminal-path equivalences and checks a mixed $H_7, H_{15}$ construction giving $f(6) \le 8{,}628$ ([local unrestricted results](erdos-64-power-of-two-cycles/CounterexampleSearch.md)). Historical priority of these reformulations and construction is unverified.

[Zhou, Theorems 1-2](https://airaxiv.com/papers/view/2608.0018/) already gives $\ell \ge 2h + 8$ for a counterexample minimal in order and then size, where $\ell$ counts degree-3 vertices and $h$ counts higher-degree vertices. The [local counting argument](erdos-64-power-of-two-cycles/DegreeComponents.md) also bounds the number of vertices outside a packing of disjoint triangles as the degree-3 fraction nears two thirds.

For a triangle factor in a cubic graph, Salehi Nowbandegani et al. already proved the cycle lift from length $r$ to every length from $2r$ through $3r$ ([earlier cubic lift, Corollary 7](https://arxiv.org/pdf/1109.5398#page=5)). The [triangle-packing proof](erdos-64-power-of-two-cycles/DegreeComponents.md#contracting-disjoint-triangles) here also handles heavy corners and uncovered vertices in a globally minimal counterexample.

Finally, the treewidth-3 proof gives a 4-, 8-, or 16-cycle avoiding any chosen edge at minimum degree 3, with a 34-vertex cubic example reaching 16. It uses [Bodlaender](https://cgi.di.uoa.gr/~sgk/teaching/GT/Bodlaender98-bt.pdf) Theorem 35 for the 3-tree completion; a hand proof sorts the pieces at a triangle into six shapes, and Lean checks the finite profile calculation. Rooted searches rule out every counterexample on at most 41 vertices, extending Ducoffe and Dumitru's check by one order, while separator searches allow arbitrary maximum degree. A binary matrix argument and cubic terminal checks raise the lower bound for a cubic bipartite counterexample to 136 vertices. Historical priority for the exact treewidth and order-41 results is unverified. Local write-ups:

* [Treewidth result](erdos-64-power-of-two-cycles/TreewidthThree.md)
* [Order 41](erdos-64-power-of-two-cycles/Order41.md)
* [Unrestricted separator reduction](erdos-64-power-of-two-cycles/Separators.md)
* [Binary descent](erdos-64-power-of-two-cycles/AlgebraicDescent.md)
* [Cubic bipartite bounds](erdos-64-power-of-two-cycles/BipartiteBounds.md)
* [Cubic minor and recursive substitution results](erdos-64-power-of-two-cycles/RecursiveGadgets.md)

## Erdős #556, three-color nine-cycle Ramsey number

Checked **23 November 2026**. Radziszowski's survey lists $R_3(C_9)$ as the first open odd-cycle case and records the lower bound 33 ([Ramsey survey, §6.3.1](https://www.cs.rit.edu/~spr/ElJC/ejcram18.pdf#page=61)). [Kohayakawa, Simonovits, and Skokan](https://users.renyi.hu/~miki/KohaSimSkokGraco.pdf) proved the exact formula for all sufficiently large odd cycle lengths. The [local Lean project](erdos-556-cycle-ramsey/) proves the $n = 9$ case assuming 15 vertices in $K_{33}$ miss one color. Historical priority for that conditional result is unverified.

## Erdős #617, missing colors in cliques

Erdős and Gyárfás posed the general conjecture and proved the 3- and 4-color cases ([original paper](https://doi.org/10.1016/S0012-365X(98)00323-9)). [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/617.lean) lists the full statement as open. A separate [five-color verification](https://github.com/RamazanKara/erdos-617-r5-formal-verification) covers five colors. Priority for the extra results in this package is unverified.

## Erdős #677, equal LCMs of six consecutive integers

Checked **23 November 2026**. Let $M(n,k)$ be the LCM of $n+1$ through $n+k$. Erdős asked about separated blocks in 1979 ([Erdős, *Some Unconventional Problems in Number Theory*, p. 67, item 2](https://www.renyi.hu/~p_erdos/1979-22.pdf)). The [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/78bc92237b4bcf5ec812a52d07364aa74773bfe2/FormalConjectures/ErdosProblems/677.lean) also includes adjacent disjoint blocks and quantifies over all positive lengths.

The [July write-up](https://erdosproblemaday.com/day/677-lcm-bridge) lists the overlapping pairs $(3,4), (5,6), (13,15)$ and reduces the remaining length-6 case to four cubic equations. [Danesh and Bianchetti, *Prime-Power Transport and a Three-Site Reduction*](https://ijmttjournal.org/archive/IJMTT-V72I9P101) also rule out configurations with at most two active progression sites at lengths 5 and 6.

This folder computes the integral points on all four curves and checks the classification in Lean under the explicit affine-point hypothesis, while the global bound uses David's theorem and external arithmetic ([proof and verification boundary](erdos-677-equal-lcms/cubic/LengthSix.md)). Searches for equal block LCMs, scaled products of six consecutive integers, scaled binomial coefficients, and the cubic $x(x-1)(x-3)$ found no earlier complete classification in the checked sources. Historical priority is unverified.

Lengths 3 and 4 were checked on **24 November 2026**. The July write-up reports both classifications too: at length 3 it gives only $(2,3)$ via a unit equation in $\mathbb Z[\sqrt[3]{2}]$ (checked there through $n \le 200{,}000$), and at length 4 it gives only $(1,2)$ via a Pell equation with a congruence and quadratic-reciprocity certificate. Danesh and Bianchetti state that their method rules out lengths 3 and 4, and [Ponnudurai (1975)](https://doi.org/10.1112/jlms/s2-10.2.232) solved $Y(Y+1)(Y+2)(Y+3) = 3X(X+1)(X+2)(X+3)$.

This project gives Lean proofs of both classifications with no external computation ([local proofs](erdos-677-equal-lcms/LengthThreeAndFour.md)). The Formal Conjectures file leaves the general statement open and proves only a test lemma for Erdős's two mixed-length examples. An [earlier Lean toolkit](https://github.com/qrdlgit/erdos677), posted to the [forum thread](https://www.erdosproblems.com/forum/thread/677) on 31 March 2026, proves prime-power lemmas and finiteness for each fixed length and gap, without classifying any fixed length. A web search found no earlier Lean proof of either length; first-formalization status is unverified.

## Erdős #708, interval products for six integers

Checked **23 November 2026**. Let $A$ be a set of six distinct integers at least 2 and set $M = \max A$. Every block of $M$ consecutive integers contains at most eight distinct entries whose product is divisible by $\prod_{a\in A}a$, and some blocks require eight. Whether $g(n) \le 2n$ holds in general is still open ([problem statement](https://www.erdosproblems.com/708)).

C. Bergström's manuscript of **19 November 2026** already proves $g(6) = 8$ ([Bergström, Proposition 3 and Theorems 6 and 12](https://doi.org/10.5281/zenodo.24366897)). Proposition 3 gives the lower-bound example, and Theorem 12 proves the upper bound using a finite certificate through $M = 3481$. The Lean proof here adapts that example and uses Bergström's cumulative-gcd rule from Theorem 6, stopping its finite check over 6-element sets at $M = 69$ ([local proof and witness](erdos-708-six/README.md)).

John Tripodo proved $g(4) = 5$ and $g(5) = 6$ in Lean ([Tripodo's preprint](https://hexagonmath.org/pdf/2611.00694v1)). The 6-element proof imports those upper bounds from his [pinned Lean source](https://github.com/jjtripodo-lgtm/erdos-708-g4-g5/tree/00fbb23c3084daa88ea420aa9c74177127d5283f).

## Erdős #835, coloring subsets

Comparison updated **23 November 2026**. At $k = 16$, the [September 28 argument](https://www.erdosproblems.com/forum/thread/835#post-9219) rules out point symmetries of orders 19, 23, 29, and 31. Separate [Steiner-system computations](https://github.com/veljjanoski/erdos835) rule out two groups acting on a single Steiner system. This folder proves restrictions on involutions, point symmetries of orders 11 and 13, and regular abelian groups acting on a coloring ([local proofs and comparison with earlier work](erdos-835-coloring-subsets/README.md#relation-to-earlier-work)). An earlier result on automorphisms of $S(4,5,21)$ by [Kolotoğlu and Magliveras (2014)](https://onlinelibrary.wiley.com/doi/10.1002/jcd.21370) also implies the order-11 exclusion and the exclusion of a single 13-cycle. The unrestricted coloring problem is still open.

## Erdős #602, countable sets with no singleton intersections

Checked **25 November 2026**. Komjáth's question, published by Erdős in 1987 ([Erdős 1987, item 12](https://www.renyi.hu/~p_erdos/1987-28.pdf)), asks whether every family of countably infinite sets with finite pairwise intersections, none of size 1, has Property B ([formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/602.lean#L78)). This project proves the unrestricted statement ([sources and credits](erdos-602-property-b/Erdos602.lean)). Two limited searches found no earlier formal or informal proof and no published theorem that implies it. Earlier work covered finite families (Lovász), countable families and families with a minimal hitting set or a suitable well-ordering (Ahlswede-Khachatrian, P. L. Erdős, Soukup), and uniformly bounded intersections (Miller, Erdős-Hajnal, Komjáth). Every ingredient of the proof is known; what appears new is how they are combined. [Komjáth 1989](https://doi.org/10.1016/S0195-6698(89)80071-X) was read only in abstract, and partial work was public in grandchallenge/MATHSOLVE on 24 November.

## Erdős #1066, minimum distances in higher dimensions

Checked **25 November 2026**. Pollack (1985) reports that Erdős asked for a proof or disproof of $g_d(n) > cn/d$ ([formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/1066.lean#L126)). This project disproves it for a constant independent of $d$ and $n$ ([sources and credits](erdos-1066-higher-dimensions/Erdos1066.lean)). **The result is a short corollary of D. de Caen's 2000 construction of $2(d+1)^2/9$ equiangular lines ([de Caen](https://doi.org/10.37236/1533)).** Three limited searches, the last using equiangular-line terms, found no one who had stated this conclusion, though experts may already know it. [Ismailescu, Lee, and Lee](https://arxiv.org/abs/2611.23767) used the same norm argument for one special system on 18 November 2026, and a draft repository from May 2026 conjectured the opposite. Bezdek, Naszódi, and Visy (2003), the main unread source, and the problem's forum posts still need checking. See also [Kalai's survey](https://arxiv.org/abs/1505.04952).

## Erdős #344, the square root of 2N variant

Checked **25 November 2026**. The headline problem, with some absolute constant, was proved by [Szemerédi and Vu](https://doi.org/10.4007/annals.2006.163.1) (2006; see also Chen 2003) and already has a public Lean proof. The constant $\sqrt2$ goes back to [Folkman](https://doi.org/10.4153/CJM-1966-065-2) (1966) and is listed as open in the [formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/344.lean#L71). Two limited searches found no earlier proof. Much of the argument sits close to published work: a theorem of [Bergelson and Simmons](https://arxiv.org/abs/1507.02208) (2017) appears to give Case 2 under a gcd condition, and Case 1 is close to a lemma of [Fan](https://arxiv.org/abs/2607.14071) (2026). Unproved remarks by Hegyvári (2000) and Chen (2003) conflict or may conflict with the theorem. See [sources and credits](erdos-344-sqrt-two/Erdos344.lean).

## Erdős #211, the constant one sixth

Checked **25 November 2026**. In [Erdős 1984](https://users.renyi.hu/~p_erdos/1984-18.pdf), Erdős wondered whether $1/6$ is possible in Beck's theorem and suggested looking for a counterexample first ([formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/211.lean#L67)). Two limited searches found no earlier disproof and no published point set with $o(n)$ points on any line and fewer than about $n^2/6$ lines. The line count itself is not claimed as new math: for a close relative of this point set it follows from Schmidt's 1998 count of primitive sublattices ([Schmidt's theorem, as quoted](https://arxiv.org/abs/0810.0234)). The book of Brass, Moser, and Pach and the papers of Schmidt and Beck were not consulted. See also [de Zeeuw](https://arxiv.org/abs/1802.08015) and [sources and credits](erdos-211-one-sixth/Erdos211.lean).

## Erdős #387, Schinzel's conjecture for large k

Checked **25 November 2026**. The headline problem was answered by [Bui, Naprienko, Pratt, and Zaharescu](https://arxiv.org/abs/2605.21221). Schinzel's Problem P 217 ([Schinzel 1958](https://doi.org/10.4064/cm-5-2-198-204)) is a separate question ([formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/387.lean#L62)). No earlier proof for all large $k$ was found. In [Erdős 1985](https://users.renyi.hu/~p_erdos/1985-27.pdf), Erdős wrote that Lacampagne and Selfridge "probably can find such n for every k ≠ p^α"; no paper was found, and it is not known what they had. The main tools (reducing to a cover, an auxiliary prime, and large primes at the end) come from Schinzel and Erdős. MathSciNet, Guy B34, and Erdős, Lacampagne, and Selfridge (1993) were not checked. See [sources and credits](erdos-387-schinzel/Erdos387.lean).

## Erdős #338, restricted order bounded by the order

Checked **25 November 2026**. Two limited searches found no earlier bound on the restricted order that depends only on the order ([Erdős-Graham 1980](https://static.renyi.hu/~p_erdos/1980-22.pdf), [formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/338.lean#L97)). The proof follows the strategy of [Chen, Yang, and Zhao](https://github.com/csq20180327/Erdos338) (18 November 2026), who characterize which bases have a restricted order; their proofs appear to yield a uniform bound by compactness, so this bound is well within reach of their method. Earlier examples appear in [Veljjanoski's note](https://github.com/veljjanoski/erdos338) of 1 October 2026. Hegyvári, Hennecart, and Plagne (2003) was not available. See [sources and credits](erdos-338-restricted-order/Erdos338.lean).

## Written on the Wall II, Graph Conjecture 133

Checked **24 November 2026**. DeLaViña's Graffiti.pc catalogue lists #133 as open ([catalogue, #133](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)). This project proves partial results for the earlier floored form. Formal Conjectures dropped the floor in September 2026 after reading the source brackets as grouping ([upstream change](https://github.com/google-deepmind/formal-conjectures/commit/5faef0c4dc3d226f8f9a9fc8f581b6221283eb6e)).

Haoyu Chen handled graphs containing a 4-cycle and all floors through 2, and proved restrictions at floor 3 ([Chen's report](https://doi.org/10.5281/zenodo.22054835)). Kuber Mehta's Lean development covers further special classes and gives a conditional reduction for regular triangle-free graphs ([Mehta's regular and low-average results](https://github.com/Kuberwastaken/c5-k4/blob/f0f912c17bde0aa1b1f4b59845cf018eea696452/results/expansion/method_v09_133_regular.md)). This folder checks all floors through 4, every order through 29, and the bipartite and regular cases at any order ([local theorems](written-on-the-wall-133/README.md)). Priority of these partial results is unverified.

The radius estimate used here comes from Erdős, Saks, and Sós, Theorem 2.2, with the proof credited to Fan Chung ([paper](https://real.mtak.hu/110576/1/1-s2.0-0095895686900286-main.pdf#page=4)). This project adapts KitaKen1's Lean [formalization](https://github.com/KitaKen1/wowii-graph-conjecture-31-lean/blob/a948e9fc07e11b786aee8dadb1376b4d938454d6/lean/GraphConjecture31.lean) of that estimate.

<a id="seven-cycle"></a>

## Seven-cycle threshold R₃²(C₇) = 11

**Audited statement:** every 3-edge-coloring of `K_n` contains a 7-cycle with at most two cyclic color changes exactly when `n ≥ 11`. Changes include the last-to-first edge transition. Using at most two colors is a weaker condition.

Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz ask about the odd-cycle family in [Problem 22](https://arxiv.org/html/2607.03243v1#Thmtheorem22). Their main asymptotic even-cycle theorem does not cover this finite case. The [arXiv record](https://arxiv.org/abs/2607.03243) lists v1, submitted 3 July 2026. The colored-K₄ construction template is already in their paper; the lower bound here specializes it.

No earlier proof of `R₃²(C₇) = 11` or matching Lean formalization was found. This result does not settle the full odd-cycle problem.

## Book Ramsey number $R(B_{63},B_{64})$

Checked **23 November 2026**. A book $B_k$ is $k$ triangles sharing one edge. Dai and Lin's conference-matrix construction gives a 252-vertex graph avoiding $B_{63}$ in both colors ([Dai and Lin, Theorem 1.1](https://arxiv.org/html/2606.07214v1)), which the Lean certificate checks explicitly.

Rousseau and Sheehan's upper bound $R(B_{n-1},B_n) \le 4n - 1$ gives 255 at $n = 64$. Chung and Wesley list this case as open ([Chung and Wesley, introduction and Appendix A](https://arxiv.org/html/2610.36522v1)). A 254-vertex graph avoiding a red $B_{63}$ and a blue $B_{64}$ would prove equality.

Lean also rules out identical circulant layers joined by a circulant cross block ([local obstruction](book-ramsey/CayleyObstruction.lean)), covering both groups of order 254. Ruling out every vertex-transitive graph of order 254 additionally relies on [McKay and Praeger, Theorem 1(b)](https://users.cecs.anu.edu.au/~bdm/papers/cheryl1.pdf) for $2p$ with $p = 127 \equiv 3 \pmod 4$.

## Classical Ramsey number $R(3,10)$

Checked **23 November 2026** (updated **25 November 2026**). Geoffrey Exoo's 39-vertex triangle-free graph (167 edges) with no independent 10-set gives $R(3,10) \ge 40$ ([Exoo (1989)](https://doi.org/10.1137/0402043), [Exoo's matrix](https://cs.indstate.edu/ge/RAMSEY/r3.10.39)). The Lean project kernel-checks Exoo's matrix, rules out extending it by one vertex, kernel-checks a second non-isomorphic 39-vertex witness (172 edges) and Kalbfleisch's unique 35-vertex $R(3,9,35)$ circulant $C_{35}(\{1,7,11,16\})$, and formalizes weighted Mantel's theorem plus the resulting 9-regular vs. $|E(G - N[v])| \le 180 - 9d$ dichotomy for $R(3,10,40)$. Vigleik Angeltveit proved $R(3,10) \le 41$ in an exhaustive computation using weighted-Mantel / blow-up bounds ([Angeltveit (2025), Theorem 1](https://doi.org/10.37236/12936)). Whether $R(3,10)$ is 40 or 41 is still open.

Harborth and Krause reported in 2003 that 38 is the largest triangle-free circulant graph with no independent 10-set ([Harborth and Krause, Table 1](https://www.researchgate.net/profile/Heiko-Harborth/publication/265670071_Ramsey_numbers_for_circulant_colorings/links/617430c6eef53e51e1d63351/Ramsey-numbers-for-circulant-colorings.pdf)), and Coniglio et al. reproduced this in 2026 ([Coniglio et al., Table 8](https://arxiv.org/html/2608.18769v1#S8.T8)). The [local proofs](ramsey-3-10/) check the order-40 circulant exclusion and graphs with a simultaneous rotation of two 20-vertex cycles in Lean, and add standalone C++23 checks outside the Lean kernel covering all 14 groups of order 40 (Cayley graphs), all 5 groups of order 20 (two-orbit bi-Cayley graphs), and degree-4 vertices via $C_{35}(\{1,7,11,16\})$.

[Li et al. (2025)](https://ijcai.org/proceedings/2025/292) (Li, Duggan, Bright, and Ganesh) gave independently checkable certificates for the exhaustive searches behind $R(3,8)$ and $R(3,9)$. For $R(3,10)$, the Lean theorem here proves that the unrestricted 40-vertex SAT formula is satisfiable exactly when a counterexample exists, though its satisfiability remains open.

## No three in line on the 75 × 75 grid

Checked **23 November 2026**. Thomas Prellberg found a 148-point set on the 74 × 74 grid on 20 July 2026 ([Flammenkamp's discovery notes](https://wwwhomes.uni-bielefeld.de/achim/no3in/readme.html#C), [74 × 74 configuration data](https://wwwhomes.uni-bielefeld.de/achim/no3in/download/configurations/n74_rot4.few)). The same points fit on 75 × 75. Flammenkamp's [28 October table](https://wwwhomes.uni-bielefeld.de/achim/no3in/table.html) lists full sets for sizes 74, 76, and 78 and leaves 75 blank.

Lean checks the first 148-point set in the data file ([local proofs](no-three-in-line-75/)). At most two points fit in each row, giving the upper bound 150. Lean also proves that every 150-point solution must drop two points of this set whose row indices differ by at least 32. Whether 150 points are reachable remains open here.

## Three-color prismatic T-tetromino boards

**Audited statements:** more than 60, and at least 45,083,592, labeled ternary boards of the specified 100-cell ziggurat where all 81 ordered T patterns appear once. The exact unrestricted count is not determined.

[Qiyuan Ma's v1.0](https://zenodo.org/records/23631079), published 25 October 2026, already proves existence and gives 60 labeled boards. The Zenodo version APIs returned only that single public version. The search also checked [*De Bruijn Polyominoes*, v2](https://arxiv.org/html/2405.18543v2) and [*Polyomino Density*, v1](https://arxiv.org/html/2608.29231v1), both dated 29 August 2026 in the inspected records.

No earlier proof of either stronger bound or matching Lean formalization was found. Showing boards lie outside Ma's 60-board family proves only that comparison, not absolute priority. See the folder's [detailed prior-art record](three-color-t-boards/PRIOR_ART.md).

<a id="three-column-matrices"></a>

## Three-column binary matrices (OEIS A401159)

For every `n ≥ 0`, the count of labeled `n × 3` binary matrices with at most two ones in each row and column is `(1 + n + C(n,2))³ − n⁴ + C(n,2)`. Mathar posted the expanded polynomial as a conjecture on 18 November 2026 ([OEIS revision history](https://oeis.org/history?seq=A401159)).

[Adler and Ross (2001), Corollary 1, equation (6)](https://adler.ieor.berkeley.edu/ilans_pubs/coupons_2001.pdf#page=2) proved a formula for the probability that independent random subsets cover a finite set. Apply it to the zero positions of the three columns: they cover all rows exactly when every row has at most two ones, and plugging in the allowed column choices gives the stated formula.

Mathar derived a rectangle recurrence in 2014 and tabulated the three-column counts for `n = 3, ..., 9` ([Mathar, §2 and Table 2](https://oeis.org/A247158/a247158.pdf#page=2)). The search found no earlier Lean formalization of this polynomial.

## Manabe's subtraction game at residue one

Checked **27 November 2026**. For moves 3, 8, and $11k+1$, where $k \ge 1$, Manabe predicts that the Grundy sequence has a positive preperiod. The Lean proof shows that the value 3 occurs exactly once, at heap $11k+4$, and that the least preperiod is $11k+5$. The optional bridge verifies the singleton statement for Manabe's original Lean definition. [Example 1 and the necessity conjecture](https://arxiv.org/html/2609.05358v2#S1) · [Lean proof](manabe-residue-one/ResidueOne.lean) · [Bridge](manabe-residue-one/ManabeBridge.lean)

Searches for this exact move set and for general results on three-move subtraction games found no earlier public proof of the singleton statement for every positive $k$. The REUF project describes proofs in regions with periodicity from the start. Pan studies how adjoining a move affects periodicity and gives exact formulas for several other bases in Theorem 12. [REUF project notes](https://github.com/ZacharyHenderson111/AIM2024/blob/0083e70bc0145e1aaef2cd77fa72fef20557fa6f/AIMsummarypaper/AIMJuly2024summary.tex#L381-L386) · [Pan, §8](https://arxiv.org/html/2611.31336v1#S8.SS2)

## Manabe's subtraction game

Checked **23 November 2026**. For the move set `{3, 8, 11k+7}` with `k ≥ 1`, the only heap with Grundy value 3 has size `11k+10`. Manabe predicts a positive preperiod for this residue in [Manabe, arXiv:2609.05358v2, Example 1](https://arxiv.org/html/2609.05358v2#S1), and the singleton theorem proves that prediction for every `k ≥ 1`.

The [REUF working notes](https://github.com/ZacharyHenderson111/AIM2024/blob/main/CollectiveNotes/oldVerifiedCases/verifiedcases2023.tex#L374-L418) give a proposed formula whose repeating block specializes to the same one here. No earlier proof of the exact singleton statement for all positive `k` was found.

## Binomial recurrence (OEIS A026019)

Checked **23 November 2026** and re-audited **26 November 2026**. For `a(n) = C(3n,n) − C(3n,n−3)` (taking binomial coefficients with negative lower index as zero), [`A026019.recurrence`](a026019-binomial-recurrence/A026019.lean) proves the three-term recurrence attributed to Mathar (20 June 2013) for every `n ≥ 2`.

Georg Fischer's first-order recurrence implementation entered jOEIS on **6 November 2026**, before this project ([introducing commit](https://github.com/archmageirvine/joeis/commit/06f94740c2d0d4b0815dedce8d41dd008ef0c1b8), [dated source](https://github.com/archmageirvine/joeis/blob/06f94740c2d0d4b0815dedce8d41dd008ef0c1b8/src/irvine/oeis/a026/A026019.java)). An exact polynomial calculation in the audit confirms that this earlier recurrence implies the three-term recurrence. The inspected source has no derivation or proof-assistant certificate.

One day after this folder's initial commit (23 November 2026), Robert Israel independently verified the exact conjecture via Maple's `simplify` command on Math StackExchange ([question 5156049](https://math.stackexchange.com/questions/5156049/mathars-recurrence-conjecture), **24 November 2026**) and updated [OEIS A026019](https://oeis.org/A026019) (revision 30, 24-25 November 2026). No earlier Lean formalization was found; first-formalization status is unverified, and this folder contributes a checked Lean proof rather than a first mathematical solution. See the project's [detailed prior-art audit](a026019-binomial-recurrence/PRIOR_ART.md) for the algebraic check, established methods, sources, and search limits.

## Nonlinear-to-linear recurrence (OEIS A176755)

Checked **23 November 2026** and re-audited **26 November 2026**. For the integer sequence `a₀ = 1`, `a₁ = 3`, `aₙ₊₁ = Σₚ₌₀ⁿ aₚaₙ₋ₚ − 2` for `n ≥ 1`, [`A176755.mathar`](a176755-linear-recurrence/A176755.lean) proves Mathar's five-term recurrence for every `n ≥ 4`.

[OEIS A176604](https://oeis.org/A176604) credits Georg Fischer with a proof for 85 related sequences on **26 January 2020** and links [the derivation](https://oeis.org/A176604/a176604_2.txt). That file returned HTTP 403 during this check, so only OEIS's attribution was seen. Fischer committed his A176755 implementation to jOEIS on **25 January 2020** ([dated source](https://github.com/archmageirvine/joeis/blob/e072e99444a75d6f2a1d48100932e999994d5a48/src/irvine/oeis/a176/A176755.java)). The implemented six-term recurrence is `Rₙ − Rₙ₋₁ = 0`, where `Rₙ` is Mathar's five-term left-hand side; since `R₄ = 260 − 330 + 28 + 42 = 0`, it implies Mathar's recurrence.

In addition, Artūras Dubickas (*Recurrence Formulas for Choulet Sequences*, *Mathematics* 14(12): 2177, **17 June 2026**, [10.3390/math14122177](https://doi.org/10.3390/math14122177)) directly proved the exact five-term recurrence for all $k = 0$ Choulet sequences (covering A176755), and Tong Niu ([arXiv:2605.04369](https://arxiv.org/abs/2605.04369), **6 May 2026**) published the same generating-function and differential-equation proof method for the sibling sequence A176677. This folder is an independent Lean proof of a result already covered by prior work, with no first-formalization claim. See the project's [prior-work notes](a176755-linear-recurrence/README.md#prior-work-and-attribution).

## Arctangent-sum conjecture

Checked **23 November 2026**. Amdeberhan, Medina, and Moll conjectured that $x_n = \tan(\sum_{k=1}^n \arctan k)$ is never an integer for $n \ge 5$. Ono proved that $O(\log N)$ positive indices up to $N$ give integers ([Ono's paper](https://arxiv.org/abs/2607.05739)). [Formal Conjectures statement and proof references](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/Arxiv/%C2%AB2607.05739%C2%BB/TanArctanSum/) links the earlier Lean formalization of Ono's results and lists the conjecture as open.

The Lean proof here sharpens the count to $O((\log N)^{3/4})$ and checks that only $n = 1, 2, 3, 4$ give integers among positive indices through $10^6$ ([project theorems](arctangent-sum/ArctanSum.lean)).

## E670 at order 10

**Audited statement:** no 10-element magma satisfies `y*(x*((x*y)*y)) = x` universally.

Checked **23 November 2026**. The live [spectrum data](https://ohaithe.re/equational_theories/research/data/spectrum.json), last modified **5 November 2026**, lists `[2,3,6,7,8]` as E670's excluded orders and 10 as its smallest undecided order, with no pending proofs. The retrieved response matches the hash saved in the [filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json). The [pinned order-ten report](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/order_ten_followup_20261007.md#what-remains-at-ten) leaves both E670 and E677 open at order 10. For E670, its [search data](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/data/spectrum/order_ten_followup_20261007.json) record 61 of 97 first-row cases refuted and 36 undecided under budgets of at most 100,000 conflicts. The catalogue and reports live on the `definability-negative` branch of the fork `Timeroot/equational_theories`, outside the main repository. That branch was at `199f75c2aa71ff0e112a8a38faf0680f252d33a4` on the check date, two commits past the pinned revision, and neither later commit touches E670.

No earlier order-10 exclusion was found. The law belongs to the Equational Theories Project, and the choice of element 0, the first-row normal form, and the exclusions at other orders belong to that spectrum work; this folder claims only the order-10 proof. Web searches for the equation number with "order 10", for the written-out law, and for the theorem names an upstream exclusion would use (`not_order_670_10`, `exclude_670_10`) found no proof. Searches of the public Zulip stream for `670`, `E670`, and the dual `2937` found no message about order 10; the latest spectrum summary there, by Alex Meiburg on 7 October 2026, lists E670 as cofinite with no finite cutoff worked out. See [Lean proof](E670-order-10/E670/Main.lean) and [project notes](E670-order-10/README.md).

## Frankl's union-closed sets conjecture

**Audited statement:** every finite union-closed family $\mathcal{F}$ of finite sets containing at least one nonempty set has an element belonging to at least $(1533 / 4000)\,|\mathcal{F}| = 0.38325\,|\mathcal{F}|$ sets of $\mathcal{F}$.

Checked **25 November 2026**. Justin Gilmer (`arXiv:2211.09055`, 2022) proved the first constant lower bound ($0.01$) via an entropy argument; several groups soon raised it to $(3 - \sqrt{5})/2 \approx 0.38197$. Jingbo Liu (`arXiv:2405.00807`, 2024) pushed the bound to $0.382709$ via conditionally i.i.d. couplings. Yunjiang Jiang (`arXiv:2609.08291`) and Simone Costa and Ankan Sadhu (`arXiv:2610.02295`) reached $0.3828852549667978$, just below the Costa-Sadhu single-coordinate entropy barrier $c_* \approx 0.38288525996679$. An unrefereed preprint of Ankan Sadhu and Touko Ursin introduced the fibre-inequality, peeling, and subset-averaging framework and claimed $c_* + 9.2 \times 10^{-5}$. On 18-19 November 2026, Quantavane announced a computer-assisted bound $c_* + 2.9 \times 10^{-4} \approx 0.38317526$ using single-order shared-budget accounting and a Cauchy-Schwarz bound on low-entropy fibres (with paper and arXiv preprint not yet posted at the time of check).

The local Lean 4 proof builds on the Sadhu-Ursin and single-order shared-budget framework, simplifies the local inequality suite (removing $J_b$, $F_{\mathrm{pos}}$, `Line2`, `Cut1`, and Option C), and proves the stronger bound $1533 / 4000 = 0.38325 > c_* + 3.647 \times 10^{-4}$ with every analytic, 1D, 2D, covariance, and polytope inequality checked inside Lean's kernel (`decide`, no `native_decide`). No earlier proof of $0.38325$ or Lean formalization of a bound past $c_*$ was found in the sources checked; the conjectured constant $1/2$ is still open. See [Costa-Sadhu (`arXiv:2610.02295`)](https://arxiv.org/abs/2610.02295), [Jiang (`arXiv:2609.08291`)](https://arxiv.org/abs/2609.08291), the [Quantavane announcement](https://quantavane.com/results/union-closed-sets/), the [Lean proof](union-closed-sets/UCBound/Main.lean), and the [project notes](union-closed-sets/README.md).

## Covering every trio among 14 people

Checked **26 November 2026**. The La Jolla data give $24\le C(14,6,3)\le25$. Dai, Li and Toulouse report a 24-group arrangement with one uncovered trio. The two C++ verifiers in this repository rule out complete coverage with 24 groups. [La Jolla Covering Repository](https://zenodo.org/records/24119701) · [Dai, Li and Toulouse](https://w1.cirrelt.ca/~toulouse/CD-BL-MT.pdf) · [Proof and reproduction commands](research/covering-14-6-3/)

## Search scope and limits

This audit checked primary papers, version records, published code and catalogues, GitHub code searches, and web searches for exact statements and alternate phrasing. Representative queries included:

```text
Equation 670 magma spectrum order 10; not_order_670_10; exclude_670_10
Zulip #Equational: 670; E670; 2937
E1486 order 15 proof; not_order_1486_15; E2126 spectrum
E1486 order 17 model; "1486" spectrum "order 17"; Zulip #Equational: 1486; 2126
E1486 order 12; not_order_1486_12; exclude_1486_12; "1486" Mace4 "size 12"
reciprocal Rado f_2(26) 2028; 2607.04373; Gaiser Ramezanpour 26
R_3^2(C_7) 11; seven cycle two colour changes; 2607.03243
prismatic T tetromino 45083592; ternary ziggurat more than 60
de Bruijn polyominoes T L; 23631079
```

It did not cover subscription databases, private repositories, unpublished work, or author correspondence. A new Lean proof can formalize a known theorem, and a machine-checked proof does not establish historical priority. Update references and labels whenever earlier work turns up.
