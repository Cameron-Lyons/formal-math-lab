# Prior proofs, originality, and research status

Checked **22 November 2026** (America/Chicago; retrievals may carry
23 November UTC timestamps). This audit compares the exact local statements
with existing mathematical proofs and public formalizations.

**One completed project is already proved in the literature:** nonattacking
kings. Four other exact results have no earlier proof located in the sources
searched. The width-12 snake and E670 order-ten entries supply no local proof.
None of these searches proves the absence of an earlier or unpublished result.

## Nonattacking kings: existing proof found

The local minimum-size and equality-classification claims are the square
specialization of **Theorem 3** in Minevich, Cunningham, Karan, and Gyllinsky,
[*Parks: A Doubly Infinite Family of NP-Complete Puzzles and Generalizations
of A002464*](https://arxiv.org/html/2411.02251v1#S7.Thmtheorem3),
submitted [4 November 2024](https://arxiv.org/abs/2411.02251).

The [OEIS A387098 data](https://github.com/oeis/oeisdata/blob/main/seq/A387/A387098.seq)
retains conjectural wording. That label does not supersede the published proof.
The project is credited as a formalization of a known theorem. No earlier
matching Lean formalization was located; no priority claim is made for it.

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

## Width-12 grid snakes: no local proof

The indexed [OEIS A397153](https://oeis.org/A397153) entry labels its generating
function conjectural. Direct OEIS retrievals were blocked with HTTP 403;
this status was checked against indexed OEIS text, not a freshly fetched
live entry. Its conjecture implies `s(n+6) = s(n) + 44` for `n ≥ 13`.

[Blondin Massé–Goupil, arXiv:2606.13155v1](https://arxiv.org/html/2606.13155v1),
submitted 11 June 2026, supplies an arbitrary-dimension generation algorithm
and exact formulas at heights 1–5, not 12. No proof of this width-12 recurrence
was located. The local directory is a research note, not a completed proof.

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
nonattacking kings 4k exactly two; A387098; Parks Shuriken arrangements
reciprocal Rado f_2(26) 2028; 2607.04373; Gaiser Ramezanpour 26
R_3^2(C_7) 11; seven cycle two colour changes; 2607.03243
prismatic T tetromino 45083592; ternary ziggurat more than 60
de Bruijn polyominoes T L; 23631079
A397153 proof; width 12 snake polyomino recurrence; 2606.13155
```

The search did not include exhaustive subscription databases, private
repositories, unpublished work, or author correspondence. A new Lean proof
can formalize a known theorem; a verified theorem does not certify historical
novelty. References and labels should be updated when earlier work is found.
