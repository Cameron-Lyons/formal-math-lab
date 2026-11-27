# A box-free coloring of the 5 × 8 × 45 grid

The first 43 layers answer the construction question. The full stack raises Genkin’s lower bound on $N(5,8)$ from 42 to 45. His upper bound of 46 leaves two possible values for the maximum. [Genkin, Lemma 2.1, Theorem 5.1 and Question 8.4](https://doi.org/10.5281/zenodo.24457907)

## Construction

Read each column mask in binary, with bit $r$ giving the color of row $r$ ($0$ blue, $1$ red). Rows are numbered 0 through 4 and columns 0 through 7.

| Seed | Column masks, left to right |
| --- | --- |
| A | 6, 25, 26, 14, 20, 21, 3, 13 |
| B | 9, 26, 22, 3, 14, 17, 28, 5 |
| C | 10, 18, 17, 22, 12, 7, 5, 25 |

Let $p=(0\ 1\ 2)(3\ 4\ 5)$ on the columns. For each seed $S$, take the 15 layers
$L_{S,h,k}(r,c)=S((r+h)\bmod 5,p^k(c))$, where $0\le h<5$ and $0\le k<3$.
The expanded stack lists the seeds in table order, with the row shift varying fastest. [All 45 layers in plain text](stack45.txt)

## Why the layers are compatible

A colored rectangle specifies two rows, two columns and one color. It can occur in at most one layer of a box-free stack. Row rotation gives two orbits of row pairs, with cyclic distances 1 and 2. Under $p$, every column pair except $\{6,7\}$ has three distinct images. Each color, row distance and nonfixed column-pair orbit therefore describes $5\cdot3=15$ colored rectangles.

The entries below record **every** monochromatic rectangle of the three seeds. Each letter denotes one rectangle in that seed. The first column is the lexicographically smallest representative of its column-pair orbit.

| Column pair | Distance 1, blue | Distance 1, red | Distance 2, blue | Distance 2, red |
| --- | --- | --- | --- | --- |
| 0, 1 | C | A | C | B |
| 0, 3 | A | A | B | B |
| 0, 4 | C | A | A | A |
| 0, 5 | B | B | C | C |
| 0, 6 | A | B | C | B |
| 0, 7 | C | C | B | A |
| 3, 4 | B | C | A | A |
| 3, 6 | C | B | C | C |
| 3, 7 | B | A | B | A |
| 6, 7 | — | — | — | — |

Each of the 36 occupied entries expands into 15 distinct rectangles. Across all 45 layers, each of those $36\cdot15=540$ rectangles occurs exactly once. A monochromatic box would require a repeat.

This particular stack cannot be extended by appending a layer. Only the 20 colored rectangles on columns 6 and 7 remain unused. In the first six columns of any new layer, each column contains at least four same-color row pairs. Those 24 or more occurrences repeat one of the 20 choices of row pair and color, producing a rectangle on two of the first six columns.

## Upper bound

In eight columns there are at least $8\cdot4=32$ occurrences of a same-color row pair. If a given row pair has color $v$ in $e$ columns, it gives $\binom e2\ge e-1$ rectangles. Summing over the 20 choices of row pair and color gives at least $32-20=12$ rectangles per layer. The grid has $2\binom52\binom82=560$ colored rectangle positions, so every box-free stack has height at most $\lfloor560/12\rfloor=46$. [Genkin, Lemma 2.1 and equation (2)](https://doi.org/10.5281/zenodo.24457907)

## Reproduce

Run `lake build` in this directory with Lean 4.36.0. The kernel checks both `BoxFree5x8.coloring45_boxFree` and the exact rectangle coverage in `BoxFree5x8.rectangle_coverage` directly from the three seeds. The theorem `BoxFree5x8.exists_boxFree_43` follows by restriction. Genkin’s independent `check_boxfree.py` also accepts the plain-text stack and reports zero monochromatic boxes. [Lean construction and proof](BoxFree5x8.lean) · [Genkin’s checker in supplementary.zip](https://zenodo.org/records/24457907)
