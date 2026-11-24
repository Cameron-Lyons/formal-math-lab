# Box-free colorings of the 6 × 7 grid

`BoxFree.exists_boxFree_iff` proves that a 6 × 7 × n grid admits a red-blue coloring without a monochromatic box exactly when n ≤ 52. Genkin constructed 50 layers and asked whether the upper bound of 52 could be attained. [Exact-height theorem](BoxFree.lean) · [Genkin, Question 8.1](https://zenodo.org/records/24457907)

The 52-layer coloring is written one layer per line, with six rows of seven bits. A monochromatic box would repeat a colored rectangle in two layers. Lean checks the table for every such repetition. Each layer in any coloring needs at least 12 of the 630 possible colored rectangles, so 53 layers would force a repetition. [Coloring and kernel check](BoxFree/Construction.lean) · [Layer count](BoxFree/LayerBound.lean) · [Upper bound](BoxFree/Upper.lean)

Run `lake build` in this directory with Lean 4.36.0.
