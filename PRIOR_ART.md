# Prior proofs, originality, and research status

Checked **22 November 2026** (America/Chicago; retrievals may carry
23 November UTC timestamps). This audit compares the exact local statements
with existing mathematical proofs and public formalizations.

For E1486, unit fractions, seven-cycles, and T-tetromino boards, the search
found no earlier proof of the exact headline results. The three-column matrix
formula follows from an earlier inclusion–exclusion theorem. The A026019
recurrence follows from a first-order recurrence already implemented in jOEIS;
its first-proof status is unverified. The A176755 recurrence is covered by
Georg Fischer’s January 2020 general recurrence.
For E670 at order 10, the search of **23 November 2026** likewise found no earlier proof.
For the 17-element model of E1486, the search of the same date found no earlier model.
For E1486 at order 12, the search of the same date found no earlier exclusion and no model.
For the 26-element model of E1486, the search of **24 November 2026** found no earlier model.
For E1486 at order 14, the search of the same date found no earlier exclusion and no model.
The E677 result at order ten formalizes José Brox’s January 2025 report; the search of **24 November 2026** found no earlier Lean proof.
The E17260 project supplies partial obstructions; finite nontrivial existence
remains open in the sources checked on **23 November 2026**.
The Erdős #708 project formalizes C. Bergström’s previously proved value $g(6)=8$
and uses John Tripodo’s Lean bounds for four and five integers.
For Erdős #602 and the variants of Erdős #211, #338, #344, #387 and #1066, limited searches up to **25 November 2026** found no earlier proof of the exact statements;
the #1066 result is a short corollary of D. de Caen’s theorem of 2000.
None of these searches proves the absence of an earlier or unpublished result.

## Queen domination on the 48 × 48 board

Checked **24 November 2026**. Östergård and Weakley give a 25-queen placement. Davies identifies 48 as the next open even board in §9 of his 21 November preprint. The project verifies the published placement and excludes 24 by exhaustive enumeration in compiled Lean. [Published placement, pp. 10–11](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v8i1r29/pdf/) · [Davies, §9](https://hexagonmath.org/pdf/2611.00830v1#page=19) · [Proof and checker](queen-domination-48/README.md)

The SAT project gives a second, independent proof of $\gamma(Q_{48}) = 25$ with Davies' frame method, and also $i(Q_{48}) = 25$ for independent dominating sets; Östergård and Weakley had both numbers in {24, 25}. No earlier determination of $i(Q_{48})$ was found, but only Davies' paper and a brief web search were consulted. [Proof and certificates](queen-domination-48-sat/README.md)

## Box-free colorings of the 6 × 7 grid

Checked **24 November 2026**. Genkin’s version 2 constructs a box-free 6 × 7 × 50 coloring and gives 52 as the upper bound. Question 8.1 asks whether the bound can be attained. The local project supplies an explicit 52-layer coloring and a Lean proof of the exact maximum. [Genkin, Theorem 5.1 and Question 8.1](https://zenodo.org/records/24457907) · [Coloring](box-free-6x7/BoxFree/Construction.lean) · [Exact-height theorem](box-free-6x7/BoxFree.lean)

## Two triples producing nine squares

Checked **24 November 2026**. Dujella poses the six-integer question as Problem 1.4. Batta, Hajdu and Pongrácz identify the case of three vertices on each side as open. The local Lean theorem rules out solutions in which both triples span a factor of at most 1,000. Priority of this bound is unverified. [Dujella, Problem 1.4](https://web.math.pmf.unizg.hr/~duje/pdf/open2.pdf#page=2) · [Batta, Hajdu and Pongrácz, §6](https://arxiv.org/html/2410.20120v1#S6) · [Lean proof](square-triples/SquareTriples/Ratio.lean)

## Nine-bit snake-in-the-box

Checked **24 November 2026**. Orland et al. published 131 inequivalent induced
paths of 191 edges in the nine-dimensional cube. They report that none admits
a one-edge extension and ask whether a 192-step path exists. Kunt, Koch, and
Park also identify dimension nine as the smallest open case.
[Orland et al., §8](https://arxiv.org/html/2607.15270v3#S8) · [Published records at the pinned revision](https://github.com/Math-AI-Caltech/Snake-in-the-Box/blob/46c765399353a588ea50444a5d6610f53102b1c2/record_snakes.csv.zip) · [Kunt, Koch, and Park](https://arxiv.org/abs/2611.25268)

The Lean project retains the first 156 steps of each published path in both
orientations. Its `native_decide` checks exclude a 192-step completion and
place every 191-step completion in one of the 131 classes. Kernel reduction
also excludes 192 steps when the first 171 steps are retained. A separate
kernel proof shows that a 191-step path is inequivalent to every published
path if the distances back to its starting endpoint after steps 1 through 17
agree in both orientations. [Prefix exclusion](nine-bit-snake/Results.lean) · [Kernel check](nine-bit-snake/KernelChecks.lean) · [Classification and endpoint test](nine-bit-snake/Closure.lean)

## Two squares of each side from 1 through 21

Checked **24 November 2026**. Friedman’s table gives bounds of two through five
on the minimum number of copies of each size needed to tile a rectangle.
On 22 November he revised problem 10 and retained the two-copy case for
`n = 21` among the open cases. [Results table](https://erich-friedman.github.io/mathmagic/0505.html) · [Open problem 10](https://erich-friedman.github.io/mathmagic/unsolved.html) · [Dated revision](https://github.com/erich-friedman/erich-friedman.github.io/commit/4072f4a7ec4aacba7590ddd5ccb016a922ea594c)

Searches by dimensions, area, square inventory, and the three-squares-per-row
argument found no earlier proof excluding 43 × 154. Priority of that exclusion
remains unconfirmed. The Lean reduction leaves 77 × 86 open. [Width-43 proof](consecutive-squares-21/Width43.lean) · [Reduction](consecutive-squares-21/Bridge.lean)

## Five 30-sided Go First Dice

Checked **24 November 2026**. The Go First Dice team lists as open whether five
30-sided dice labeled with 1 through 150 can give all 120 rankings equal odds.
The October preprint by Gavenčiak, Haeupler, and Rozhoň credits Paul Meyer with a
five-die construction using 60 faces per die. [Researchers’ open question](http://gofirstdice.ericharshbarger.org/doku.php?id=open_questions#d30) · [October preprint, §1.2](https://arxiv.org/html/2610.15421v1#S1.SS2)

The team reports an exhaustive exclusion of every column-grouped labeling,
where each consecutive group of five labels includes one face from each die.
This covers the fifteen mirrored permutation blocks excluded by the local Lean proof.
The search found no earlier statement of the local modulo-four condition. Its priority
remains unconfirmed. [Researchers’ solution counts](http://gofirstdice.ericharshbarger.org/doku.php?id=homogeneous_solutions#column_paired) · [Mirrored-block proof](five-30-sided-dice/MirroredObstruction.lean) · [Modulo-four proof](five-30-sided-dice/EqualCuts.lean)

## Three integer cubes summing to 114

Checked **23 November 2026**. Booker and Sutherland report a search for 114 using cube roots modulo the pair sum. Grantham and Walsh describe a related number-field search, and Welsh gives the general correspondence between cubic ideals and pairs of roots. The local lemma gives an elementary family outside the absolute norms of $\mathbb Z[\sqrt[3]{114}]$. Its historical priority is unverified. [Booker–Sutherland, §5.2](https://arxiv.org/pdf/2007.01209#page=14) · [Grantham–Walsh](https://arxiv.org/abs/2211.12149) · [Welsh, Theorem 3](https://arxiv.org/abs/2008.00538) · [Local proof](three-cubes-114/TernaryFamily.lean)

## E677 implies E255 at order nine

Checked **23 November 2026**. On 10 December 2024, José Brox reported that an exhaustive Mace4 search excluded nine-element magmas satisfying E677 and failing E255. The local Lean proof independently checks this case using an LRAT certificate. [Brox’s search report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#487358914) · [Lean proof](E677-E255-order-9/Nine.lean)

## E677 at order ten

**Audited statement:** no 10-element magma satisfies
`x = y*(x*((y*x)*y))` universally. In particular E677 implies E255 at order
ten.

Checked **24 November 2026**. Both statements were reported earlier from
searches that were not machine-checked. On 22 December 2024 José Brox wrote
that size 10 was ruled out for E677 magmas failing E255. On 12 January 2025 he
wrote: "There are no models whatsoever of 677 in size 10 (39h in Mace4)." Rudi
Schneider reported on 21 November 2025 that his own search program enumerates
all E677 magmas through size 11. Jihoon Hyun wrote the same day that CaDiCaL
had given a negative result for size 10 in about six hours; the runs he
describes elsewhere in the thread encode E677 together with a failure of E255.
The ICARM Equation 677 database lists none of size 10, and its commentary cites
Brox's search and a six-hour CaDiCaL run.
[Brox, 22 December 2024](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#490346469) · [Brox, 12 January 2025](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#493229385) · [Schneider](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#558558838) · [Hyun](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#558568783) · [ICARM database](https://eq677.icarm.cloud/size/10)

Two later reports describe SAT refutations of the weaker statement, with DRAT
certificates accepted by drat-trim: an issue on the Equational Theories
Project's main repository dated 22 July 2026, and a prove2.me mission page.
Neither publishes its certificates, and neither is a Lean proof.
[Issue 1464](https://github.com/teorth/equational_theories/issues/1464) · [Mission page](https://prove2.me/missions/Equational_Magmas%3A_E677_%E2%86%92_E255_(finite_case))

No Lean proof of either statement was located in the main repository, in the
fork `Timeroot/equational_theories`, in other public E677 repositories found by
search, or in the public Equational channel of the Lean Zulip. The fork's live
[spectrum data](https://ohaithe.re/equational_theories/research/data/spectrum.json),
last modified **5 November 2026**, list Lean exclusions for E677 at orders 2,
3, 4, 6 and 8 and give 10 as its smallest undecided order. Its
[order-ten report](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/docs/order_ten_followup_20261007.md#what-remains-at-ten)
records the E677 searches at ten as unfinished. The local contribution is a
Lean-checked proof of Brox's January 2025 report, not a new mathematical
result. First-formalization status is unverified.
[Lean proof](E677-E255-order-9/Ten.lean)

## E1486 at order 15

**Audited statement:** no 15-element magma satisfies
`(y*x)*(x*(z*z)) = x` universally.

The [pinned research note](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/1486_graph_spectrum.md)
and [live spectrum data](https://ohaithe.re/equational_theories/research/data/spectrum.json)
both list 15 among E1486's unresolved orders. The live data response was last
modified **5 November 2026** and lists `[12,14,15,17,26]` for both E1486 and its
dual E2126, with no pending proofs. A
[filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json)
preserves the response hash and headers.

No earlier order-15 exclusion was located. The source law, square-row
identities, and earlier spectrum results belong to the Equational Theories
Project; the local claim is the specific order-15 exclusion, not the whole
spectrum or the first formal study of E1486.

## E1486 at order 17

**Audited statement:** some 17-element magma satisfies
`(y*x)*(x*(z*z)) = x` universally.

Checked **23 November 2026** (24 November UTC). The pinned research note and
live spectrum data cited for order 15 also list 17 among E1486's unresolved
orders. The live response is unchanged since **5 November 2026** and matches the
hash in the [filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json).
The note's [search data](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/data/spectrum/1486_search_followup.json)
record one attempt at order 17: a CaDiCaL run on the full law that reached its
60-second limit with result `UNKNOWN`.

The note, catalogue, and data are developed on a branch of a fork. The main
project's [commentary](https://github.com/teorth/equational_theories/blob/02b063b67143a897f070803482691c820770501d/commentary/Equation1486.md)
says only that the finite spectrum is unknown. Its
[equation list](https://github.com/teorth/equational_theories/blob/02b063b67143a897f070803482691c820770501d/data/equations.txt#L1486)
gives Equation 1486 as `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`, the law checked here.

No earlier 17-element model or order-17 exclusion was located in the fork, in
the main repository's issues and pull requests, or in the public Equational
channel of the Lean Zulip. The
[earlier discussion](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Understanding.20Finite.201486.20Magmas.html)
of sporadic models does not mention order 17. The local claim is this one model,
not the spectrum. [Lean proof](E1486-order-15/Simple/Order17.lean)

## E1486 at order 12

**Audited statement:** no 12-element magma satisfies
`(y*x)*(x*(z*z)) = x` universally.

Checked **23 November 2026** (24 November UTC). The pinned research note and
live spectrum data cited for order 15 also list 12 among E1486's unresolved
orders. The live response is unchanged since **5 November 2026** and matches the
hash in the [filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json).
The note is unchanged at the fork's latest research revision,
[`199f75c2`](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/docs/1486_graph_spectrum.md).

The recorded attempts at order 12 did not decide it. The note's
[search data](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/data/spectrum/1486_search_followup.json)
record three CaDiCaL runs, one unrestricted and two with a normalized row; each
reached its 60-second limit with result `UNKNOWN`. A later
[search campaign](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/docs/spectrum_search_campaign_20261011.md)
ran four restricted cases for 900 seconds each. One returned `UNSAT` and three
timed out; its report says "No order-12 existence or nonexistence claim follows
from this partial search." On the Lean Zulip, Bruno Le Floch
[reported](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Writing.20a.20paper.20on.20the.20spectrum.20of.20an.20equational.20law/near/627564683)
on 28 September 2026 stopping a Mace4 search at size 12 after 14 hours.

No earlier order-12 exclusion or 12-element model was located in the fork, in
the main repository's issues and pull requests, or in the public Equational
channel of the Lean Zulip. The local claim is this one exclusion, not the
spectrum. [Lean proof](E1486-order-15/Simple/Order12/NoTable.lean)

## E1486 at order 26

**Audited statement:** some 26-element magma satisfies
`(y*x)*(x*(z*z)) = x` universally.

Checked **24 November 2026**. The pinned research note and live spectrum data
cited for order 15 also list 26 among E1486's unresolved orders. The live
response is unchanged since **5 November 2026** and matches the hash in the
[filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json).
The note is unchanged at the fork's latest research revision,
[`199f75c2`](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/docs/1486_graph_spectrum.md).

The recorded attempts at order 26 did not decide it. The note reports that a
uniform two-fold lift of the known 13-element model is impossible, and that a
solver refuted three nonuniform alternatives. It adds that these reports "do
not imply that every 26-element model is impossible." The note's
[search data](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/data/spectrum/1486_search_followup.json)
record one CaDiCaL run on the full law at order 26, which reached its 60-second
limit with result `UNKNOWN`.

No earlier 26-element model or order-26 exclusion was located in the fork, by
an issue and pull-request search of the fork and of the main repository, or by
web search. The archived Zulip
[discussion](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Understanding.20Finite.201486.20Magmas.html)
of sporadic models does not mention order 26. The local claim is this one
model, not the spectrum. [Lean proof](E1486-order-15/Simple/Order26.lean)

## E1486 at order 14

**Audited statement:** no 14-element magma satisfies
`(y*x)*(x*(z*z)) = x` universally.

Checked **24 November 2026**. The pinned research note and live spectrum data
cited for order 15 also list 14 among E1486's unresolved orders. The live
response is unchanged since **5 November 2026** and matches the hash in the
[filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json).
The note is unchanged at the fork's latest research revision, `199f75c2`.

The note's
[search data](https://github.com/Timeroot/equational_theories/blob/199f75c2aa71ff0e112a8a38faf0680f252d33a4/data/spectrum/1486_search_followup.json)
record one attempt at order 14: a CaDiCaL run on the full law that reached its
60-second limit with result `UNKNOWN`. No earlier order-14 exclusion or
14-element model was located in the fork, by an issue and pull-request search
of the fork and of the main repository, in the public Equational channel of the
Lean Zulip, or by web search.
[Lean proof](E1486-order-15/Simple/Order14/NoTable.lean)

Orders 12, 14, 15, 17 and 26 are the five that the live spectrum data list as
unresolved for E1486. The E1486 record in that data marks two bounds from the
fork's Lean development as proved: no model at orders 2, 3, 5, 6, 7, 8 and 10,
and a model at every other positive order outside those five. Combined with the
five local results, the orders with no model are exactly 2, 3, 5, 6, 7, 8, 10,
12, 14 and 15. This combination is not checked as one theorem, and the fork's
proofs were not re-verified here.

## E17260: partial results, finite existence unresolved

Checked **23 November 2026**. The law is
`x = (y*x)*(z*(x*(z*z)))` for every `x,y,z`. The local Lean theorems show
that a model has at most one element if it has an idempotent, surjective
squaring, either cancellation law, or an affine operation on a commutative
additive monoid. They also rule out square-map cycles of length two and
establish finite counting bounds. **They do not settle finite nontrivial
existence.** See the [project and theorem endpoints](E17260-partial-results/).

The Equational Theories Project's
[catalogue at the inspected 23 November 2026 revision](https://github.com/teorth/equational_theories/blob/02b063b67143a897f070803482691c820770501d/blueprint/src/chapter/order_5.tex#L99-L110)
still lists finite existence for E17260 and its dual E28740 as unknown.
[*Trace-Tree Magmas*, arXiv v3, revised 22 September 2026](https://arxiv.org/html/2609.05690v3#S7.SS2)
provides Lean-certified infinite models and explicitly leaves the finite
question open in Table 4 and [Section 9](https://arxiv.org/html/2609.05690v3#S9).
These infinite models are prior work, not a result of this project.

The 16 December 2024 discussion already reports
[exhaustive exclusion through order 10](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Some.20results.20from.20order.205.html#489163277)
and [absence of finite linear models, including noncommutative coefficients](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Some.20results.20from.20order.205.html#489207891).
The local affine proof works without finiteness, but no novelty claim is made.
The novelty of the other partial obstructions and their first-formalization
status have not been established. Local searches at orders 11–20 were
inconclusive and do not improve the known finite exclusion bound.

## Integer cubic $z^2+y^2z+x^3=2$

Checked **24 November 2026**. Grechuk lists infinitude of integer triples as
open in Table 6. Epoch reports polynomial families for related cubics and asks
for three integer triples on this cubic with distinct $x$ and $|x|>10^{50}$.
[Grechuk, §5](https://arxiv.org/html/2404.08518v11#S5) ·
[Epoch’s challenge](https://epoch.ai/frontiermath/open-problems/small-diophantine) ·
[Epoch’s two constructions](https://epoch.ai/files/open-problems/small-diophantine-two-families.pdf)

The local project gives a degree bound for polynomial families through an
integer triple and a family with $x,z$ integral and $y$ of reduced denominator
13. Historical priority for these partial results is unverified. [Project proof and checker](integer-cubic/README.md)

Lean proves that a rational quartic substitution on $u^2-3v^2=1$ with
nonconstant $x$ and one integral seed would give infinitely many integer
triples. The bounded coefficient searches found no such substitution in the
classes tested. A separate Lean theorem excludes the quintic substitution
$az=2-r^3$, $x=r-p^2z$ for nonzero rational $a$ when $r,p$ have simple poles
at both conjugate ends of a nonsplit Pell conic and all coordinates are regular
away from those ends. Priority for these results is unverified.
[Quartic theorem](integer-cubic/pell/MixedPellAmplification.lean) ·
[Search scope](integer-cubic/pell/QuarticFreeMark.md) ·
[Quintic exclusion](integer-cubic/pell/QuinticSquareObstruction.lean)

<a id="reciprocal-rado"></a>

## Reciprocal Rado number f₂(26) = 2028

**Audited statement:** every two-coloring of `[1,N]` forces the 26-summand
reciprocal equation, with repetitions allowed, exactly when `N ≥ 2028`.

[Gaiser–Ramezanpour, arXiv:2607.04373v1](https://arxiv.org/html/2607.04373v1)
supplies the general lower bound and some identities used here. Its computed
table stops at 25; its proved family `k = 3·2^m` does not include 26.
The [record](https://arxiv.org/abs/2607.04373) lists only v1, submitted
5 July 2026. No earlier proof of the exact 26-summand upper bound was located.

Earlier formal work exists: Korea Superintelligence Labs'
[Machina Mathematica](https://lean.up.railway.app/) lists certified reciprocal
Rado values at smaller parameters and a general lower bound
([data](https://lean.up.railway.app/api/data)). Fabian Arevalo's
[research note](https://fabianarevalo.com/reciprocal-rado) and
[repository](https://github.com/farev/Matematica/blob/main/conjectures/reciprocal-rado/README.md)
also treat smaller values; the general even-parameter mechanism is a sketch,
not a proof covering 26. This collection does not claim the first Lean work
on reciprocal Rado numbers.

## Erdős #556, three-color nine-cycle Ramsey number

Checked **23 November 2026**. Radziszowski’s survey lists $R_3(C_9)$ as the
first open odd-cycle case and records the lower bound 33. Kohayakawa,
Simonovits, and Skokan prove the exact formula for sufficiently large odd
cycle lengths. The local result for $n=9$ assumes a set of 15 vertices in
$K_{33}$ omits a color. Historical priority for that conditional result
is unverified. [Ramsey survey, §6.3.1](https://www.cs.rit.edu/~spr/ElJC/ejcram18.pdf#page=61) ·
[Kohayakawa, Simonovits, and Skokan](https://users.renyi.hu/~miki/KohaSimSkokGraco.pdf) ·
[Local Lean project](erdos-556-cycle-ramsey/)

## Erdős #617, missing colors in cliques

Erdős and Gyárfás posed the unrestricted conjecture and proved the three- and four-color cases. The Formal Conjectures collection lists the general statement as open. A separate formal verification treats five colors. Priority for the additional results in this package is unverified. [Original paper](https://doi.org/10.1016/S0012-365X(98)00323-9) · [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/617.lean) · [Five-color verification](https://github.com/RamazanKara/erdos-617-r5-formal-verification)

## Erdős #677, equal LCMs of six consecutive integers

Checked **23 November 2026**. With $M(n,k)$ the LCM of $n+1$ through $n+k$,
Erdős asked about separated blocks in 1979. The published Lean statement
includes adjacent disjoint blocks and quantifies over all positive lengths.
[Erdős, *Some Unconventional Problems in Number Theory*, p. 67, item 2](https://www.renyi.hu/~p_erdos/1979-22.pdf) · [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/78bc92237b4bcf5ec812a52d07364aa74773bfe2/FormalConjectures/ErdosProblems/677.lean)

The July 2026 write-up records the overlapping pairs $(3,4),(5,6),(13,15)$
and reduces the remaining length-six case to four cubic equations. Danesh and
Bianchetti also exclude configurations with at most two active progression
sites at lengths five and six. [July write-up](https://erdosproblemaday.com/day/677-lcm-bridge) · [Danesh and Bianchetti, *Prime-Power Transport and a Three-Site Reduction*](https://ijmttjournal.org/archive/IJMTT-V72I9P101)

The project supplies the integral-point calculation on all four curves and
checks the resulting classification in Lean under the explicit affine-point
hypothesis. The global bound uses David’s theorem and external arithmetic.
Searches under equal block LCMs, scaled products of six consecutive integers,
scaled binomial coefficients, and the cubic $x(x-1)(x-3)$ located no earlier
complete classification in the sources inspected. Historical priority remains
unverified. [Proof and verification boundary](erdos-677-equal-lcms/cubic/LengthSix.md)

Lengths three and four were checked on **24 November 2026**. The July write-up
also reports both classifications. At length three it gives the single pair
$(2,3)$, attributed to a unit equation in $\mathbb Z[\sqrt[3]{2}]$ and
confirmed there by a search through $n\le200{,}000$. At length four it gives
the single pair $(1,2)$, from a Pell equation with a congruence and
quadratic-reciprocity certificate. Danesh and Bianchetti state that their
method excludes lengths three and four. Ponnudurai solved
$Y(Y+1)(Y+2)(Y+3)=3X(X+1)(X+2)(X+3)$ in 1975. The local contribution is a Lean
proof of each classification with no external computation. The Formal
Conjectures file leaves the general statement open and proves only a test lemma
for Erdős's two mixed-length examples. An earlier public Lean toolkit, posted
to the problem's forum thread on 31 March 2026, proves prime-power lemmas and
finiteness for each fixed length and gap. It has no classification at a fixed
length. A web search located no earlier Lean proof of either length.
First-formalization status is unverified.
[Ponnudurai (1975)](https://doi.org/10.1112/jlms/s2-10.2.232) · [Earlier Lean toolkit](https://github.com/qrdlgit/erdos677) · [Forum thread](https://www.erdosproblems.com/forum/thread/677) · [Local proofs](erdos-677-equal-lcms/LengthThreeAndFour.md)

## Erdős #708, interval products for six integers

Checked **23 November 2026**. Let $A$ be a set of six distinct integers at
least two and set $M=\max A$. From every block of $M$ consecutive integers one
can choose at most eight distinct entries whose product is divisible by
$\prod_{a\in A}a$. Some blocks require eight. The general question whether
$g(n)\le 2n$ remains open.
[Problem statement](https://www.erdosproblems.com/708)

C. Bergström’s manuscript of **19 November 2026** already gives $g(6)=8$.
Proposition 3 supplies the lower-bound example. Theorem 12 proves the upper
bound using a finite certificate through $M=3481$. The local Lean proof adapts
that example and uses Bergström’s cumulative-gcd rule from Theorem 6. Its
finite check over six-element sets stops at $M=69$.
[Bergström, Proposition 3 and Theorems 6 and 12](https://doi.org/10.5281/zenodo.24366897) ·
[Local proof and witness](erdos-708-six/README.md)

John Tripodo proved $g(4)=5$ and $g(5)=6$ in Lean. The six-element proof
imports those upper bounds from the revision cited in his preprint.
[Tripodo’s preprint](https://hexagonmath.org/pdf/2611.00694v1) ·
[Pinned Lean source](https://github.com/jjtripodo-lgtm/erdos-708-g4-g5/tree/00fbb23c3084daa88ea420aa9c74177127d5283f)

## Erdős #835, coloring subsets

Comparison updated **23 November 2026**. At $k=16$, the September 2026 discussion excludes point symmetries of orders 19, 23, 29, and 31. Separate computations exclude two groups acting on a single Steiner system. The local project proves restrictions on involutions, point symmetries of orders 11 and 13, and regular abelian groups acting on a coloring. An earlier result on automorphisms of $S(4,5,21)$ also implies the order-11 exclusion and the exclusion of a single 13-cycle. The unrestricted coloring problem remains open. [Kolotoğlu and Magliveras (2014)](https://onlinelibrary.wiley.com/doi/10.1002/jcd.21370) · [September 28 argument](https://www.erdosproblems.com/forum/thread/835#post-9219) · [Steiner-system computations](https://github.com/veljjanoski/erdos835) · [Local proofs and comparison with earlier work](erdos-835-coloring-subsets/README.md#relation-to-earlier-work)

<a id="seven-cycle"></a>

## Erdős #602, countable sets with no singleton intersections

Checked **25 November 2026**. Komjáth’s question, published by Erdős in 1987, asks whether every family of countably infinite sets with finite pairwise intersections, none of size 1, has Property B. The local project proves the unrestricted statement. Two limited searches found no earlier proof, formal or informal, and no published theorem that implies it. Known before: finite families (Lovász), countable families and families with a minimal hitting set or a suitable well-ordering (Ahlswede–Khachatrian, P. L. Erdős, Soukup), and uniformly bounded intersections (Miller, Erdős–Hajnal, Komjáth). Every ingredient of the proof is known; what appears to be new is the combination. Komjáth’s paper of 1989 was read only in abstract, and partial work was public in grandchallenge/MATHSOLVE on 24 November. [Erdős 1987, item 12](https://www.renyi.hu/~p_erdos/1987-28.pdf) · [Komjáth 1989](https://doi.org/10.1016/S0195-6698(89)80071-X) · [Formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/602.lean#L78) · [Sources and credits](erdos-602-property-b/Erdos602.lean)

## Erdős #1066, minimum distances in higher dimensions

Checked **25 November 2026**. Pollack (1985) reports that Erdős asked for a proof or disproof of $g_d(n) > cn/d$. The local project disproves it for a constant independent of $d$ and $n$. **The result is a short corollary of D. de Caen’s construction of $2(d+1)^2/9$ equiangular lines (2000).** Three limited searches, the last with the vocabulary of equiangular lines, found no one who had drawn this conclusion, but it may well be known to experts. The norm argument is already used for one special system by Ismailescu, Lee and Lee on 18 November 2026. A draft repository of May 2026 conjectures the opposite. Bezdek, Naszódi and Visy (2003), the main unread source, and the problem’s forum posts should be checked. [de Caen](https://doi.org/10.37236/1533) · [Ismailescu, Lee and Lee](https://arxiv.org/abs/2611.23767) · [Kalai’s survey](https://arxiv.org/abs/1505.04952) · [Formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/1066.lean#L126) · [Sources and credits](erdos-1066-higher-dimensions/Erdos1066.lean)

## Erdős #344, the square root of 2N variant

Checked **25 November 2026**. The headline problem, with some absolute constant, is due to Szemerédi and Vu (2006; see also Chen 2003), and has a public Lean proof. For the constant $\sqrt2$, which is listed as open by Formal Conjectures, two limited searches found no earlier proof. The question goes back to Folkman (1966). Much is close to published work: a theorem of Bergelson and Simmons (2017) appears to give Case 2 under a gcd condition, and Case 1 is close to a lemma of Fan (2026). Remarks of Hegyvári (2000) and Chen (2003), without proof, conflict or may conflict with the theorem. [Folkman](https://doi.org/10.4153/CJM-1966-065-2) · [Szemerédi–Vu](https://doi.org/10.4007/annals.2006.163.1) · [Bergelson–Simmons](https://arxiv.org/abs/1507.02208) · [Fan](https://arxiv.org/abs/2607.14071) · [Formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/344.lean#L71) · [Sources and credits](erdos-344-sqrt-two/Erdos344.lean)

## Erdős #211, the constant one sixth

Checked **25 November 2026**. Erdős (1984) wondered whether the constant $1/6$ is possible in Beck’s theorem and advised to look for a counterexample first. Two limited searches found no earlier disproof and no published point set with $o(n)$ points on any line and fewer than about $n^2/6$ lines. The line count is not claimed as new mathematics: for a close relative of the point set it follows from Schmidt’s count of primitive sublattices (1998). The book of Brass, Moser and Pach and the papers of Schmidt and Beck were not opened. [Erdős 1984](https://users.renyi.hu/~p_erdos/1984-18.pdf) · [de Zeeuw](https://arxiv.org/abs/1802.08015) · [Schmidt’s theorem, as quoted](https://arxiv.org/abs/0810.0234) · [Formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/211.lean#L67) · [Sources and credits](erdos-211-one-sixth/Erdos211.lean)

## Erdős #387, Schinzel’s conjecture for large k

Checked **25 November 2026**. The headline problem was answered by Bui, Naprienko, Pratt and Zaharescu. Schinzel’s Problem P 217 (1958) is a separate question. No earlier proof for all large $k$ was found. Erdős wrote in 1985 that Lacampagne and Selfridge “probably can find such n for every k ≠ p^α”; no paper was found, and it is not known what they had. The main devices (the reduction to a cover, an auxiliary prime, large primes at the end) are due to Schinzel and Erdős. MathSciNet, Guy B34 and Erdős, Lacampagne and Selfridge (1993) were not seen. [Schinzel 1958](https://doi.org/10.4064/cm-5-2-198-204) · [Erdős 1985](https://users.renyi.hu/~p_erdos/1985-27.pdf) · [Bui, Naprienko, Pratt and Zaharescu](https://arxiv.org/abs/2605.21221) · [Formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/387.lean#L62) · [Sources and credits](erdos-387-schinzel/Erdos387.lean)

## Erdős #338, restricted order bounded by the order

Checked **25 November 2026**. Two limited searches found no earlier bound on the restricted order that depends only on the order. The strategy is that of Chen, Yang and Zhao (18 November 2026), who characterize the bases with a restricted order; their proofs appear to give such a bound by a compactness argument, so the uniform bound should not be described as out of reach of their method. Earlier instances are in Veljjanoski’s note of 1 October 2026. Hegyvári, Hennecart and Plagne (2003) was not available. [Erdős–Graham 1980](https://static.renyi.hu/~p_erdos/1980-22.pdf) · [Chen, Yang and Zhao](https://github.com/csq20180327/Erdos338) · [Veljjanoski](https://github.com/veljjanoski/erdos338) · [Formal statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/338.lean#L97) · [Sources and credits](erdos-338-restricted-order/Erdos338.lean)

## Written on the Wall II, Graph Conjecture 133

Checked **24 November 2026**. DeLaViña’s Graffiti.pc catalogue lists #133 as open. The local project proves partial results for the earlier floored formulation. Formal Conjectures removed the floor in September 2026 after interpreting the source brackets as grouping. [Catalogue, #133](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) · [Upstream change](https://github.com/google-deepmind/formal-conjectures/commit/5faef0c4dc3d226f8f9a9fc8f581b6221283eb6e)

Haoyu Chen treats graphs containing a four-cycle and all floors through two, and derives restrictions at floor three. Kuber Mehta’s Lean development treats further special classes and gives a conditional reduction for regular triangle-free graphs. The local project verifies all floors through four, every order through 29, and the bipartite and regular cases at arbitrary order. Priority of these partial results is unverified. [Chen’s report](https://doi.org/10.5281/zenodo.22054835) · [Mehta’s regular and low-average results](https://github.com/Kuberwastaken/c5-k4/blob/f0f912c17bde0aa1b1f4b59845cf018eea696452/results/expansion/method_v09_133_regular.md) · [Local theorems](written-on-the-wall-133/README.md)

The radius estimate used here appears in Erdős, Saks and Sós, Theorem 2.2, with the proof credited to Fan Chung. The project adapts KitaKen1’s Lean formalization of that estimate. [Paper](https://real.mtak.hu/110576/1/1-s2.0-0095895686900286-main.pdf#page=4) · [Formalization](https://github.com/KitaKen1/wowii-graph-conjecture-31-lean/blob/a948e9fc07e11b786aee8dadb1376b4d938454d6/lean/GraphConjecture31.lean)

## Seven-cycle threshold R₃²(C₇) = 11

**Audited statement:** every three-edge-coloring of `K_n` contains a seven-cycle
with at most two cyclic color changes exactly when `n ≥ 11`. Changes include
the last-to-first edge transition. Using at most two colors is a weaker condition.

Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz's
[Problem 22](https://arxiv.org/html/2607.03243v1#Thmtheorem22) asks about the
odd-cycle family. The paper's main asymptotic even-cycle theorem does not
give this exact finite case. Its [record](https://arxiv.org/abs/2607.03243)
lists v1, submitted 3 July 2026. The colored-K₄ construction template is
already present there; the local lower bound specializes it.

No earlier proof of `R₃²(C₇) = 11`, or matching Lean formalization, was located.
This result does not settle the full odd-cycle problem.

## Book Ramsey number $R(B_{63},B_{64})$

Checked **23 November 2026**. A book $B_k$ consists of $k$ triangles sharing an edge.
Dai and Lin’s conference-matrix construction gives a graph on 252 vertices
that avoids $B_{63}$ in both colors. The local Lean certificate checks the
explicit graph. [Dai and Lin, Theorem 1.1](https://arxiv.org/html/2606.07214v1)

Rousseau and Sheehan’s general upper bound $R(B_{n-1},B_n) \le 4n-1$ gives 255
at $n=64$. Chung and Wesley list this case as open. A 254-vertex graph avoiding
a red $B_{63}$ and a blue $B_{64}$ would establish equality.
[Chung and Wesley, introduction and Appendix A](https://arxiv.org/html/2610.36522v1)

Lean also rules out identical circulant layers joined by a circulant cross
block. This covers both groups of order 254. The exclusion of every
vertex-transitive graph at this order additionally uses McKay and Praeger’s
classification for $2p$ with $p=127\equiv3\pmod4$.
[Local obstruction](book-ramsey/CayleyObstruction.lean) · [McKay and Praeger, Theorem 1(b)](https://users.cecs.anu.edu.au/~bdm/papers/cheryl1.pdf)

## Classical Ramsey number $R(3,10)$

Checked **23 November 2026** (updated **25 November 2026**). Geoffrey Exoo's 39-vertex triangle-free graph (167 edges) with no independent ten-set gives $R(3,10)\ge 40$. The local Lean project kernel-checks Exoo's matrix, rules out extending that particular graph by one vertex, kernel-checks a second non-isomorphic 39-vertex witness (172 edges) and Kalbfleisch's unique 35-vertex $R(3,9,35)$ circulant $C_{35}(\{1,7,11,16\})$, and formalizes weighted Mantel's theorem and the resulting 9-regular vs. $|E(G - N[v])| \le 180 - 9d$ dichotomy for $R(3,10,40)$. Vigleik Angeltveit proved $R(3,10)\le 41$ in a separate exhaustive computation using weighted-Mantel / blow-up constraints. The unrestricted choice between 40 and 41 remains open.
[Exoo (1989)](https://doi.org/10.1137/0402043) ·
[Exoo's matrix](https://cs.indstate.edu/ge/RAMSEY/r3.10.39) ·
[Angeltveit (2025), Theorem 1](https://doi.org/10.37236/12936)

Harborth and Krause reported in 2003 that 38 is the largest order of a
triangle-free circulant graph with no independent ten-set. Coniglio and
coauthors reproduced this value in 2026. The local project verifies the
order-40 circulant exclusion and treats graphs admitting a simultaneous
rotation of two 20-vertex cycles in Lean, and includes standalone C++23
exhaustive checks outside the Lean kernel covering all 14 groups of order 40
(Cayley graphs), all 5 groups of order 20 (two-orbit bi-Cayley graphs), and
degree-4 vertices via $C_{35}(\{1,7,11,16\})$.
[Harborth and Krause, Table 1](https://www.researchgate.net/profile/Heiko-Harborth/publication/265670071_Ramsey_numbers_for_circulant_colorings/links/617430c6eef53e51e1d63351/Ramsey-numbers-for-circulant-colorings.pdf) ·
[Coniglio et al., Table 8](https://arxiv.org/html/2608.18769v1#S8.T8) ·
[Local proofs](ramsey-3-10/)

Li, Duggan, Bright, and Ganesh supplied independently checkable certificates
for the exhaustive searches used for $R(3,8)$ and $R(3,9)$. For $R(3,10)$,
the local Lean theorem proves that the unrestricted 40-vertex SAT instance is
satisfiable exactly when a counterexample exists. Its satisfiability remains
undecided. [Li et al. (2025)](https://ijcai.org/proceedings/2025/292)

## No three in line on the 75 × 75 grid

Checked **23 November 2026**. Thomas Prellberg found a 148-point configuration
on the 74 × 74 grid on 20 July 2026. The same points fit the 75 × 75 grid.
Flammenkamp’s table of 28 October records full configurations for sizes 74,
76, and 78 and leaves size 75 blank. [Flammenkamp’s discovery notes](https://wwwhomes.uni-bielefeld.de/achim/no3in/readme.html#C) ·
[74 × 74 configuration data](https://wwwhomes.uni-bielefeld.de/achim/no3in/download/configurations/n74_rot4.few) ·
[28 October table](https://wwwhomes.uni-bielefeld.de/achim/no3in/table.html)

Lean verifies the first 148-point configuration in the data file. At most
two points can occupy each row, giving the upper bound of 150. The local
proof also shows that every 150-point solution must omit two points of this
particular configuration whose row indices differ by at least 32. Whether
150 points are achievable remains open in this project. [Local proofs](no-three-in-line-75/)

## Three-color prismatic T-tetromino boards

**Audited statements:** more than 60, and at least 45,083,592, labeled
ternary boards of the specified 100-cell ziggurat with all 81 ordered T
patterns occurring once. The exact unrestricted total is not determined.

[Qiyuan Ma's v1.0](https://zenodo.org/records/23631079), published
25 October 2026, already proves existence and supplies 60 labeled boards.
The Zenodo version APIs returned that same single public version. The search
also checked [*De Bruijn Polyominoes*, v2](https://arxiv.org/html/2405.18543v2)
and [*Polyomino Density*, v1](https://arxiv.org/html/2608.29231v1), both dated
29 August 2026 in the inspected records.

No earlier proof of either stronger bound, or a matching Lean formalization,
was located. Exclusion from Ma's supplied family proves only that particular
comparison, not absolute priority. See the project's
[detailed prior-art record](three-color-t-boards/PRIOR_ART.md).

<a id="three-column-matrices"></a>

## Three-column binary matrices (OEIS A401159)

For every `n ≥ 0`, the count of labeled `n × 3` binary matrices with at most
two ones in each row and each column is `(1 + n + C(n,2))³ − n⁴ + C(n,2)`.
Mathar listed the expanded polynomial as a conjecture on 18 November 2026.
[OEIS revision history](https://oeis.org/history?seq=A401159)

Adler and Ross proved a formula for the probability that independent random
subsets cover a finite set. Apply it to the zero positions of the three columns.
They cover all rows exactly when the matrix meets the row bound. Substituting
the allowed column choices gives the stated count.
[Adler and Ross (2001), Corollary 1, equation (6)](https://adler.ieor.berkeley.edu/ilans_pubs/coupons_2001.pdf#page=2)

Mathar derived a recurrence for rectangles in 2014 and tabulated the three-column
counts for `n = 3,…,9`. The search found no earlier Lean formalization of this
specific polynomial. [Mathar, §2 and Table 2](https://oeis.org/A247158/a247158.pdf#page=2)

## Manabe’s subtraction game

Checked **23 November 2026**. For the moves `{3, 8, 11k+7}` with `k ≥ 1`,
the only heap with Grundy value 3 has size `11k+10`. Manabe predicts a
positive preperiod for this residue in Example 1. The singleton theorem
proves that prediction for every member of this family.
[Manabe, arXiv:2609.05358v2, Example 1](https://arxiv.org/html/2609.05358v2#S1)

The REUF team's working notes give a proposed formula whose repeating block
specializes to the same one here. The search found no earlier proof of the
exact singleton statement for every positive `k`.
[REUF working notes](https://github.com/ZacharyHenderson111/AIM2024/blob/main/CollectiveNotes/oldVerifiedCases/verifiedcases2023.tex#L374-L418)

## Binomial recurrence (OEIS A026019)

Checked **23 November 2026**. For `a(n) = C(3n,n) − C(3n,n−3)`, with negative
lower binomial indices interpreted as zero, the theorem
[`A026019.recurrence`](a026019-binomial-recurrence/A026019.lean) proves the exact
three-term recurrence attributed to Mathar, 20 June 2013, for every `n ≥ 2`.
The retrieved [OEIS entry](https://oeis.org/A026019) labels it a conjecture;
the live revision history was inaccessible during the search.

Georg Fischer’s first-order recurrence implementation entered jOEIS on
**6 November 2026**, before this project.
[Introducing commit](https://github.com/archmageirvine/joeis/commit/06f94740c2d0d4b0815dedce8d41dd008ef0c1b8) ·
[Dated source](https://github.com/archmageirvine/joeis/blob/06f94740c2d0d4b0815dedce8d41dd008ef0c1b8/src/irvine/oeis/a026/A026019.java)
An exact polynomial calculation in the audit verifies that this earlier
recurrence implies the three-term recurrence. The inspected implementation
contains no accompanying derivation or proof-assistant certificate.

No earlier explicit proof of the exact recurrence or matching Lean
formalization was located. Historical priority and first-formalization status
remain unverified; the contribution is a checked Lean proof. See the project's
[detailed prior-art audit](a026019-binomial-recurrence/PRIOR_ART.md) for the
algebraic comparison, established methods, sources, and search limits.

## Nonlinear-to-linear recurrence (OEIS A176755)

Checked **23 November 2026**. For the integer sequence `a₀ = 1`, `a₁ = 3`,
`aₙ₊₁ = Σₚ₌₀ⁿ aₚaₙ₋ₚ − 2` for `n ≥ 1`, the theorem
[`A176755.mathar`](a176755-linear-recurrence/A176755.lean) proves Mathar’s
five-term recurrence for every `n ≥ 4`.

[OEIS A176604](https://oeis.org/A176604) attributes a proof for 85 related
sequences to Georg Fischer, dated **26 January 2020**, and links
[the derivation](https://oeis.org/A176604/a176604_2.txt). That attachment returned
HTTP 403 during this check; its proof attribution is recorded by OEIS.
Fischer’s A176755 implementation was committed to jOEIS on **25 January 2020**:
[dated source](https://github.com/archmageirvine/joeis/blob/e072e99444a75d6f2a1d48100932e999994d5a48/src/irvine/oeis/a176/A176755.java).

The implemented six-term recurrence is exactly `Rₙ − Rₙ₋₁ = 0`, where `Rₙ`
is Mathar’s five-term left-hand side. Since the defining initial values give
`R₄ = 260 − 330 + 28 + 42 = 0`, the earlier recurrence implies the result here.
The contribution is an independently developed Lean proof of a result covered
by earlier work. No first-formalization claim is made. See the project’s
[prior-work notes](a176755-linear-recurrence/README.md#prior-work-and-attribution).

## Arctangent-sum conjecture

Checked **23 November 2026**. Amdeberhan, Medina, and Moll conjectured that
$x_n=\tan(\sum_{k=1}^n\arctan k)$ is nonintegral for every $n\geq5$.
Ono proved that $O(\log N)$ positive indices through $N$ give integer values.
Formal Conjectures links the earlier Lean formalization of Ono’s results and
lists the conjecture as open. [Ono’s paper](https://arxiv.org/abs/2607.05739) ·
[Formal Conjectures statement and proof references](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/Arxiv/%C2%AB2607.05739%C2%BB/TanArctanSum/)

The local Lean proof sharpens the count to $O((\log N)^{3/4})$ and verifies
that only $n=1,2,3,4$ give integers among positive indices through $10^6$.
[Project theorems](arctangent-sum/ArctanSum.lean)

## E670 at order 10

**Audited statement:** no 10-element magma satisfies
`y*(x*((x*y)*y)) = x` universally.

Checked **23 November 2026**. The live
[spectrum data](https://ohaithe.re/equational_theories/research/data/spectrum.json),
last modified **5 November 2026**, lists `[2,3,6,7,8]` as E670's excluded orders
and 10 as its smallest undecided order, with no pending proofs. The response
retrieved for this check has the hash preserved in the
[filtered retrieval record](research/prior-art/equational-spectrum-2026-11-22.json).
The [pinned order-ten report](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/order_ten_followup_20261007.md#what-remains-at-ten)
leaves E670 and E677 unresolved at ten. For E670 its
[search data](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/data/spectrum/order_ten_followup_20261007.json)
records 61 of the 97 first-row cases refuted and 36 undecided within budgets of
at most 100,000 conflicts. The catalogue and these reports are developed on the
`definability-negative` branch of the fork `Timeroot/equational_theories`, not
in the project's main repository. That branch had the head
`199f75c2aa71ff0e112a8a38faf0680f252d33a4` on the day of the check, two
commits after the pinned revision; neither later commit concerns E670.

No earlier order-10 exclusion was located. The law belongs to the Equational
Theories Project; the choice of the element labelled 0, the normal form of the
first row, and the exclusions at other orders belong to that spectrum work. The local
claim is the specific order-10 exclusion, not the whole spectrum. Web searches
for the equation number with “order 10”, for the law written out, and for the
theorem names an upstream exclusion would carry (`not_order_670_10`,
`exclude_670_10`) returned no proof. The project's public Zulip stream was
searched through its web-public interface for `670`, `E670` and the dual
`2937`: no message concerns order 10. The latest spectrum summary there, by
Alex Meiburg on 7 October 2026, lists E670 as cofinite with no finite cutoff
worked out.
[Lean proof](E670-order-10/E670/Main.lean) ·
[project notes](E670-order-10/README.md)

## Search scope and limits

The audit combined primary papers and version records, published code and
catalogues, GitHub code searches, and web searches for exact statements and
equivalent terminology. Representative queries included:

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

The search did not include exhaustive subscription databases, private
repositories, unpublished work, or author correspondence. A new Lean proof
can formalize a known theorem; a verified theorem does not certify historical
novelty. References and labels should be updated when earlier work is found.
