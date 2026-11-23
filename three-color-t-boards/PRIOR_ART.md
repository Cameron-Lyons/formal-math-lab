# Prior-art check for the three-color T-board lower bound

Checked on **22 November 2026**.

## Extension to the current lower bound

The collection-wide audit on the same date also searched for the current
**45,083,592-board** lower bound, using the exact number, ternary prismatic
T/L terminology, de Bruijn polyominoes, and Lean formalizations. No earlier
proof of that bound was located in Ma's current Zenodo version or the two
foundational papers listed below. This negative search does not establish
priority. Existence and the first 60 boards already have published proofs;
the unrestricted ternary total remains undetermined here. See the
[collection audit](../PRIOR_ART.md#three-color-prismatic-t-tetromino-boards).

## Original small-proof audit

**Conclusion:** no earlier published proof that there are more than 60 of
these boards was found in the sources and searches described below.
Historical priority has **not** been established conclusively. This is a
literature-search finding, not a proof that no previous proof exists.

The [mathematical proof](PROOF.md) independently establishes at least 72
valid labeled boards. It also proves that board A is outside the 60-board
family supplied by Qiyuan Ma. Those are finite mathematical claims and
have been checked in Lean. Exclusion from that family does not imply
exclusion from every construction in the literature.

## The exact question checked

The board has ten centered rows of lengths 1,3,...,19. A T has three
consecutive cells in a lower row and the cell directly above their middle.
Every ordered pattern (top, left, middle, right) over three fixed colors
must occur exactly once. Colors are labeled, the apex and orientation
are fixed, and horizontally reflected arrays count separately when unequal.

The question is whether the number of such arrays exceeds 60. It is not
the question of their exact total, of their existence alone, of binary
colorings, or of colorings for a different tetromino. The T-to-L
correspondence is relevant, so searches also included L-tetromino wording.

## Primary sources checked

1. **Qiyuan Ma, _Explicit Three- and Four-Color Prismatic T-Tetrominoes_.**
   [Zenodo record](https://zenodo.org/records/23631079), version 1.0,
   published 25 October 2026, DOI 10.5281/zenodo.23631079.
   The counting proposition supplies five symmetry families totaling 60
   labeled ternary boards. Its final counting paragraph says the exact
   ternary total is undetermined by those computations. The local
   [manuscript source](sources/main.tex) and
   [certificate](sources/anc/certificates.json) agree with that description.
   The [versions API](https://zenodo.org/api/records/23631079/versions)
   returned one public version; the
   [latest-version API](https://zenodo.org/api/records/23631079/versions/latest)
   returned the same record. The
   [record API](https://zenodo.org/api/records/23631079)
   identifies concept DOI 10.5281/zenodo.23631078 and an update timestamp
   of 2026-10-25T01:55:59.084141+00:00.

2. **D. M. Condon, Yuxin Wang, and E. Yang, _De Bruijn Polyominoes_.**
   [arXiv record](https://arxiv.org/abs/2405.18543), first posted
   28 May 2024; latest listed version v2, 29 August 2026.
   [Remark 5.4](https://arxiv.org/html/2405.18543v2#S5) discusses the
   ziggurat problem and the count of 168 binary colorings. Section 6
   relates T and L tetrominoes. Inspection did not locate a bound
   exceeding 60 for the ternary T boards at issue here.

3. **D. M. Condon, Eli B. Dugan, Laney M. Goldman, and Emily R. Williams,
   _Polyomino Density_.**
   [arXiv record](https://arxiv.org/abs/2608.29231), v1,
   29 August 2026, the only listed version when checked.
   Inspection of the [paper](https://arxiv.org/html/2608.29231v1),
   including its construction section, did not locate a result
   establishing more than 60 ternary T boards.

The two arXiv papers are the references cited in Ma's manuscript.
The fact that an exact count remains undetermined does **not** establish
that the weaker inequality “more than 60” was previously unresolved.

## Search scope

Web searches included the following queries:

```text
"Explicit Three- and Four-Color Prismatic T-Tetrominoes"
"Qiyuan Ma" "T-Tetrominoes"
"23631079" "T"
"T-tetrominoes" "60"
"T-tetromino" "three-color"
"T-tetromino" "ternary"
"T-tetromino" "prismatic"
"prismatic" "T-tetromino" "72"
"T-tetromino" "17160"
"de Bruijn polyominoes" "T" "colorings" "60"
"ziggurat" "de Bruijn"
"ziggurat" "colorings" "60"
"prismatic" "L-tetromino" "three"
"three-color" "T boards"
```

These searches found Ma's record and the foundational work above, but
no earlier published proof of the requested strict inequality. Results
about square tetrominoes or binary boards do not answer this question.

This was not an exhaustive MathSciNet, zbMATH, or citation-database
review. No authors were contacted. Unindexed publications, unpublished
work, and results under other terminology may have been missed.

## Wording supported by this check

> Six explicit representatives give 72 distinct valid labeled boards,
> and board A is outside all five of Ma's published symmetry families.
> No earlier published proof of the strict lower bound was found in
> the sources and searches checked on 22 November 2026. This establishes
> the mathematical result and novelty relative to the supplied family;
> it does not establish absolute historical priority. The exact total
> remains undetermined by this work.
