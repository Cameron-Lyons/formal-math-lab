# Prior-art check for the three-color T-board lower bound

Checked on **22 November 2026**.

## Extension to the current lower bound

The collection-wide audit on the same date also searched for the current **45,083,592-board** lower bound, using the exact number, ternary prismatic T/L terminology, de Bruijn polyominoes, and Lean formalizations. No earlier proof of that bound showed up in Ma's current Zenodo version or the two foundational papers listed below. This negative search does not settle priority. Existence and the first 60 boards already have published proofs, and the unrestricted ternary total is still unknown here. See the [collection audit](../PRIOR_ART.md#three-color-prismatic-t-tetromino-boards).

## Original small-proof audit

**Conclusion:** we found no earlier published proof that more than 60 of these boards exist in the sources and searches listed below. Historical priority is **not** confirmed. This is a literature-search result, not a proof that no earlier proof exists.

The [mathematical proof](PROOF.md) independently proves at least 72 valid labeled boards. It also proves that board A lies outside Qiyuan Ma's 60-board family. Those are finite mathematical claims, and both are checked in Lean. Being outside that family does not mean board A is outside every construction in the literature.

## The exact question checked

The board has ten centered rows of lengths 1, 3, ..., 19. A T consists of three consecutive cells in a lower row plus the cell directly above their middle. Every ordered pattern (top, left, middle, right) over three fixed colors must occur exactly once. Colors are labeled, the apex and orientation are fixed, and horizontal reflections count separately when they differ.

The question is whether there are more than 60 such boards. It is not about their exact total, existence alone, binary colorings, or a different tetromino. Because T and L tetrominoes correspond closely, the search also checked L-tetromino wording.

## Primary sources checked

1. **Qiyuan Ma, _Explicit Three- and Four-Color Prismatic T-Tetrominoes_.**
   [Zenodo record](https://zenodo.org/records/23631079), version 1.0,
   published 25 October 2026, DOI 10.5281/zenodo.23631079.
   The counting proposition gives five symmetry families totaling 60
   labeled ternary boards. Its final counting paragraph notes that the exact
   ternary total is not determined by those computations. The local
   [manuscript source](sources/main.tex) and
   [certificate](sources/anc/certificates.json) match that description.
   The [versions API](https://zenodo.org/api/records/23631079/versions)
   returned one public version, and the
   [latest-version API](https://zenodo.org/api/records/23631079/versions/latest)
   returned the same record. The
   [record API](https://zenodo.org/api/records/23631079)
   lists concept DOI 10.5281/zenodo.23631078 and an update timestamp
   of 2026-10-25T01:55:59.084141+00:00.

2. **D. M. Condon, Yuxin Wang, and E. Yang, _De Bruijn Polyominoes_.**
   [arXiv record](https://arxiv.org/abs/2405.18543), first posted
   28 May 2024; latest listed version v2, 29 August 2026.
   [Remark 5.4](https://arxiv.org/html/2405.18543v2#S5) discusses the
   ziggurat problem and the count of 168 binary colorings. Section 6
   relates T and L tetrominoes. Reading the paper turned up no bound
   above 60 for these three-color T boards.

3. **D. M. Condon, Eli B. Dugan, Laney M. Goldman, and Emily R. Williams,
   _Polyomino Density_.**
   [arXiv record](https://arxiv.org/abs/2608.29231), v1,
   29 August 2026, the only listed version when checked.
   Reading the [paper](https://arxiv.org/html/2608.29231v1),
   including its construction section, turned up no result proving
   more than 60 ternary T boards.

Ma's manuscript cites both arXiv papers. Even though the exact count is still open, that alone does **not** prove that the weaker inequality "more than 60" was previously open.

## Search scope

Web searches included these queries:

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

These queries found Ma's record and the papers above, but no earlier published proof of the strict lower bound. Results about square tetrominoes or binary boards do not answer this question.

This was not a full MathSciNet, zbMATH, or citation-database review, and we did not contact any authors. Unindexed publications, unpublished notes, or results using different terms could have been missed.

## Wording supported by this check

> Six explicit representatives give 72 distinct valid labeled boards,
> and board A lies outside all five of Ma's published symmetry families.
> No earlier published proof of the strict lower bound was found in
> the sources and searches checked on 22 November 2026. This proves
> the mathematical bound and novelty relative to Ma's published family,
> without claiming absolute historical priority. The exact total
> remains open.
