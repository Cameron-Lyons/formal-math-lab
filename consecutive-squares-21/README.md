# Tiling a rectangle with two copies of squares 1 through 21 (42 squares, Erich Friedman Open Problem 10): reduction to 77 x 86 — Lean 4 proof

**Status: reduced to a single rectangle (77 × 86); whether 77 × 86 can be tiled remains open.** Take **42 squares**: two squares of each integer side length from 1 through 21 (total area $2 \sum_{k=1}^{21} k^2 = 6{,}622$). **Erich Friedman's Math Magic Open Problem 10** asks for the minimum number of copies of each square $1 \times 1, \ldots, n \times n$ needed to tile a rectangle; the two-copy case at $n = 21$ is listed as open.

This Lean 4 project proves (`Squares42.exists_tiling_iff_77_by_86`) that **the only possible rectangle these 42 squares can tile is $77 \times 86$** (up to rotation), excluding both $22 \times 301$ and $43 \times 154$.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Erich Friedman Open Problem 10** (*Math Magic*, May 2005, case $n = 21$, two copies of squares $1, \ldots, 21$), tiling a rectangle with 42 consecutive-size squares (area 6,622), exclusion of `22 x 301` and `43 x 154`, reduction to `77 x 86` |
| **Status** | **Partial result (dimension reduction proved in Lean 4).** Excludes `22 x 301` and `43 x 154`; whether `77 x 86` admits a tiling remains open. |
| **Main Lean theorems** | `Squares42.exists_tiling_iff_77_by_86`, `Squares42.only_remaining_rectangle` ([Bridge.lean](Bridge.lean)); `Squares42.no_width_43` ([Width43.lean](Width43.lean)) |
| **Verification** | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof across all six modules) |
| **Prior-art status** | Checked **24 November 2026**: Friedman's 22 November revision keeps the two-copy $n = 21$ case open; our search found no earlier proof excluding $43 \times 154$ (priority unconfirmed). See [PRIOR_ART.md](../PRIOR_ART.md#two-squares-of-each-side-from-1-through-21). |

## Proof overview

The formal model places all 42 squares on an integer grid and requires every unit cell of the $w \times h$ rectangle to be covered exactly once ([Squares.lean](Squares.lean)). Since the total area is $6{,}622 = 2 \cdot 7 \cdot 11 \cdot 43$ and each side must be at least 21, the only candidate dimensions (with $w \le h$) are **$22 \times 301$**, **$43 \times 154$**, and **$77 \times 86$**:

* **Excluding $22 \times 301$ ([Squares.lean](Squares.lean)):** placing a $21 \times 21$ square inside width 22 leaves a $1 \times 21$ strip alongside it, which would require 21 unit squares — only two exist.
* **Excluding $43 \times 154$ ([Width43.lean](Width43.lean)):** counting row intersections across the 154 rows forces every row to intersect **exactly three** squares. The two $1 \times 1$ squares then force the two $21 \times 21$ squares to overlap in exactly 2 rows. Each of the two 19-row strips on opposite sides of that overlap then requires **both** $11 \times 11$ squares, a contradiction.

## Reproduce

Run from this directory with Lean **4.36.0** (standard library only):

```sh
lake build
```

## References

* [Erich Friedman, Math Magic — Open Problem 10](https://erich-friedman.github.io/mathmagic/unsolved.html) · [Results table (May 2005)](https://erich-friedman.github.io/mathmagic/0505.html)
* [Main theorem](Bridge.lean) · [Model & area argument](Squares.lean) · [Width-43 proof](Width43.lean)
* [Dated prior-art audit](../PRIOR_ART.md#two-squares-of-each-side-from-1-through-21)
