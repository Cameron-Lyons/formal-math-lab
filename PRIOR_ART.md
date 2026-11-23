# Prior proofs, originality, and research status

Checked **22 November 2026** (America/Chicago; retrievals may carry
23 November UTC timestamps). This audit compares the exact local statements
with existing mathematical proofs and public formalizations.

For E1486, unit fractions, seven-cycles, and T-tetromino boards, the search
found no earlier proof of the exact headline results. The three-column matrix
formula follows from an earlier inclusion–exclusion theorem. The A026019
recurrence follows from a first-order recurrence already implemented in jOEIS;
its first-proof status is unverified. The A176755 recurrence is covered by
Georg Fischer’s January 2020 general recurrence. The E670 order-ten research target
supplies no local proof.
The E17260 project supplies partial obstructions; finite nontrivial existence
remains open in the sources checked on **23 November 2026**.
None of these searches proves the absence of an earlier or unpublished result.

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

Checked **23 November 2026**. Grechuk lists infinitude of integer triples as
open in Table 6. Epoch reports polynomial families for related cubics.
[Grechuk, §5](https://arxiv.org/html/2404.08518v11#S5) ·
[Epoch’s two constructions](https://epoch.ai/files/open-problems/small-diophantine-two-families.pdf)

The local project gives a degree bound for polynomial families through an
integer triple and a family with $x,z$ integral and $y$ of reduced denominator
13. Historical priority for these partial results is unverified. [Project proof and checker](integer-cubic/README.md)

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

<a id="seven-cycle"></a>

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

## E670 on ten elements: no local proof

The live [spectrum data](https://ohaithe.re/equational_theories/research/data/spectrum.json)
still lists order 10 open for E670, without a pending proof. The
[pinned order-ten report](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/order_ten_followup_20261007.md#what-remains-at-ten)
likewise leaves E670 and E677 unresolved at ten. This collection contains no
proof project for that target.

## Search scope and limits

The audit combined primary papers and version records, published code and
catalogues, GitHub code searches, and web searches for exact statements and
equivalent terminology. Representative queries included:

```text
E1486 order 15 proof; not_order_1486_15; E2126 spectrum
reciprocal Rado f_2(26) 2028; 2607.04373; Gaiser Ramezanpour 26
R_3^2(C_7) 11; seven cycle two colour changes; 2607.03243
prismatic T tetromino 45083592; ternary ziggurat more than 60
de Bruijn polyominoes T L; 23631079
```

The search did not include exhaustive subscription databases, private
repositories, unpublished work, or author correspondence. A new Lean proof
can formalize a known theorem; a verified theorem does not certify historical
novelty. References and labels should be updated when earlier work is found.
