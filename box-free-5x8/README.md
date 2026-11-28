# A box-free coloring of the $5 \times 8 \times 45$ grid

Color every lattice point of a 3D grid of size $5 \times 8 \times n$ either blue or red. The coloring is **box-free** if no axis-aligned rectangular box $\{r_1, r_2\} \times \{c_1, c_2\} \times \{z_1, z_2\}$ ($r_1 < r_2$, $c_1 < c_2$, $z_1 < z_2$) has all 8 of its corners the same color. Thinking of the 3D grid as a vertical stack of $n$ flat $5 \times 8$ layers, a monochromatic 3D box occurs if and only if two distinct layers contain the *exact same* monochromatic $2 \times 2$ rectangle (same pair of rows, same pair of columns, and same color).

How tall can a box-free $5 \times 8 \times n$ stack get? Let $N(5, 8)$ be the maximum possible height. The construction here gives **45 layers**: its first 43 layers settle Genkin's construction question (Question 8.4), and the full stack raises Genkin's lower bound on $N(5, 8)$ from 42 to 45. Combined with Genkin's upper bound of 46, only two values remain possible: $N(5, 8) \in \{45, 46\}$ ([Genkin, Lemma 2.1, Theorem 5.1 and Question 8.4](https://doi.org/10.5281/zenodo.24457907)).

| Field | Summary |
| --- | --- |
| Problem | Maximum height $N(5, 8)$ of a box-free 2-coloring of $5 \times 8 \times n$ ([Genkin, Question 8.4](https://doi.org/10.5281/zenodo.24457907)) |
| Result | Explicit 45-layer box-free stack ($45 \le N(5, 8) \le 46$); first 43 layers answer Question 8.4 |
| Main theorems | `BoxFree5x8.coloring45_boxFree`, `BoxFree5x8.rectangle_coverage`, `BoxFree5x8.exists_boxFree_43` in [BoxFree5x8.lean](BoxFree5x8.lean) |
| Verification | `lake build` (Lean 4.36.0; pure kernel check) and independent Python check via Genkin's `check_boxfree.py` |

## The construction

Rather than listing 45 unrelated layers, the entire stack is generated symmetrically from just **three $5 \times 8$ seed layers** (A, B, and C).

Each column of a $5 \times 8$ layer has 5 bits and is written as an integer from $0$ to $31$: read the number in binary, where bit $r$ (the $2^r$ place) gives the color of row $r$ ($0$ = blue, $1$ = red), with rows numbered $0$ through $4$ and columns $0$ through $7$.

| Seed | Column masks, left to right (columns 0 to 7) |
| --- | --- |
| A | `6, 25, 26, 14, 20, 21, 3, 13` |
| B | `9, 26, 22, 3, 14, 17, 28, 5` |
| C | `10, 18, 17, 22, 12, 7, 5, 25` |

**Quick decoding example.** In Seed A:
- Column 0 has mask `6` $= 2^1 + 2^2 = (00110)_2$, so rows $1, 2$ are red and rows $0, 3, 4$ are blue.
- Column 1 has mask `25` $= 2^0 + 2^3 + 2^4 = (11001)_2$, so rows $0, 3, 4$ are red and rows $1, 2$ are blue.
- Column 2 has mask `26` $= 2^1 + 2^3 + 2^4 = (11010)_2$, so rows $1, 3, 4$ are red and rows $0, 2$ are blue.

Notice that columns 1 and 2 of Seed A are both red in rows 3 and 4, forming one red monochromatic rectangle on rows $\{3, 4\}$ and columns $\{1, 2\}$.

**Expanding the seeds into 45 layers.** Let $p = (0\ 1\ 2)(3\ 4\ 5)$ be the column permutation that cyclically rotates columns $0 \to 1 \to 2 \to 0$ and $3 \to 4 \to 5 \to 3$ while keeping columns $6$ and $7$ fixed. For each seed $S \in \{A, B, C\}$, generate $5 \times 3 = 15$ layers by cyclically shifting rows by $h$ and applying $p^k$ to the columns:

$$
L_{S, h, k}(r, c) = S\big((r + h) \bmod 5,\ p^k(c)\big), \qquad 0 \le h < 5,\ 0 \le k < 3.
$$

The expanded 45-layer stack lists the seeds in table order (A, then B, then C), with the row shift $h$ varying fastest ([All 45 layers in plain text](stack45.txt)).

## Why no monochromatic box can occur

**The big idea.** A colored rectangle is specified by two rows, two columns, and one color; to avoid monochromatic boxes, each colored rectangle can appear in at most one layer. Instead of checking $\binom{45}{2} = 990$ pairs of layers by hand, we group all colored rectangles into orbits under our symmetry group (cyclic row shifts $\times$ the column 3-cycle $p$):

- **Row pairs (2 orbits of size 5):** Arranging the 5 rows in a ring $0 - 1 - 2 - 3 - 4 - 0$, every pair of rows has cyclic distance either **1** (adjacent, like $\{0,1\}$ or $\{4,0\}$) or **2** (separated by one row, like $\{0,2\}$ or $\{1,4\}$). Row rotation maps any pair to all 5 pairs of the same cyclic distance.
- **Column pairs (9 orbits of size 3, plus 1 fixed pair):** Under $p = (0\ 1\ 2)(3\ 4\ 5)$, every pair of columns except $\{6, 7\}$ visits 3 distinct column pairs (for instance, $\{0, 1\} \to \{1, 2\} \to \{2, 0\}$).

Each choice of color, row cyclic distance, and non-fixed column-pair orbit therefore defines a family of $5 \cdot 3 = 15$ distinct colored rectangles. If a seed contains at most one rectangle from a given family—and no other seed uses that family—then the 15 rotated copies of that seed hit all 15 rectangles in the family *once each*, with zero collisions.

The table below lists **every** monochromatic rectangle occurring in the three seeds. Each letter records a single rectangle in that seed (for instance, the red rectangle on rows $\{3, 4\}$ and columns $\{1, 2\}$ of Seed A computed above appears in row `0, 1` under **Distance 1, red**). The first column gives the lexicographically smallest representative of each column-pair orbit.

| Column-pair orbit rep. | Distance 1, blue | Distance 1, red | Distance 2, blue | Distance 2, red |
| --- | --- | --- | --- | --- |
| `0, 1` | C | A | C | B |
| `0, 3` | A | A | B | B |
| `0, 4` | C | A | A | A |
| `0, 5` | B | B | C | C |
| `0, 6` | A | B | C | B |
| `0, 7` | C | C | B | A |
| `3, 4` | B | C | A | A |
| `3, 6` | C | B | C | C |
| `3, 7` | B | A | B | A |
| `6, 7` | — | — | — | — |

There are 36 occupied cells in the table, each holding a single seed letter. Every occupied entry expands into 15 distinct rectangles, so across all 45 layers those $36 \cdot 15 = 540$ rectangles occur **exactly once** each. Because a monochromatic 3D box would require some colored rectangle to appear in two different layers, the stack is box-free.

**Why a 46th layer cannot simply be appended.** Only the $2 \cdot \binom{5}{2} = 20$ colored rectangles on columns $\{6, 7\}$ remain unused. Now consider the first six columns of any candidate 46th layer. In any column of 5 cells colored with 2 colors, the color split is $(5, 0)$, $(4, 1)$, or $(3, 2)$, which yields $\binom{5}{2} = 10$, $\binom{4}{2} = 6$, or $\binom{3}{2} + \binom{2}{2} = 4$ same-color row pairs—always at least 4 per column. Across the first six columns, that gives at least $6 \cdot 4 = 24$ occurrences of a same-color row pair. Since there are only 20 possible `(row pair, color)` choices, the pigeonhole principle forces a repeat across two of the first six columns, creating a rectangle that was already used in the 45-layer stack.

## Upper bound ($N(5, 8) \le 46$)

The same counting argument gives Genkin's upper bound across all 8 columns ([Genkin, Lemma 2.1 and equation (2)](https://doi.org/10.5281/zenodo.24457907)):

1. Each of the 8 columns in a layer contains at least 4 same-color row pairs, giving at least $8 \cdot 4 = 32$ occurrences in total.
2. If a particular `(row pair, color)` choice occurs in $e$ columns of the layer, it generates $\binom{e}{2}$ monochromatic rectangles. For every integer $e \ge 0$, we have $\binom{e}{2} \ge e - 1$.
3. Summing over all $2\binom{5}{2} = 20$ choices of row pair and color yields at least $32 - 20 = 12$ monochromatic rectangles in every layer.
4. A $5 \times 8$ grid has only $2\binom{5}{2}\binom{8}{2} = 2 \cdot 10 \cdot 28 = 560$ possible colored rectangles in total.

Since no colored rectangle can repeat across layers, any box-free stack has height at most $\lfloor 560 / 12 \rfloor = 46$.

## Reproduce

Run `lake build` in this directory with Lean 4.36.0. Lean's kernel directly verifies both `BoxFree5x8.coloring45_boxFree` and the exact 540-rectangle partition in `BoxFree5x8.rectangle_coverage` straight from the three seeds, and `BoxFree5x8.exists_boxFree_43` follows by restricting to the first 43 layers. Genkin's independent `check_boxfree.py` also accepts `stack45.txt` and reports zero monochromatic boxes.

- [Lean construction and proof](BoxFree5x8.lean)
- [All 45 layers in plain text](stack45.txt)
- [Genkin's checker in supplementary.zip](https://zenodo.org/records/24457907)
