# Tiling a rectangle with two copies of squares 1 through 21

Imagine you are handed 42 square tiles: two $1 \times 1$ squares, two $2 \times 2$ squares, and so on up to two $21 \times 21$ squares. Can you pack all 42 tiles—with no gaps and no overlaps—into a single solid rectangle? This is the two-copy, $n = 21$ case of Erich Friedman's *Math Magic* Open Problem 10, which asks for the fewest copies of each square $1 \times 1, \ldots, n \times n$ needed to tile a rectangle.

The total area of the 42 tiles is $2 \sum_{k=1}^{21} k^2 = 6{,}622 = 2 \cdot 7 \cdot 11 \cdot 43$, leaving only **three** candidate rectangle shapes wide enough to hold a $21 \times 21$ square: $22 \times 301$, $43 \times 154$, and $77 \times 86$. The Lean 4 proof here (`Squares42.exists_tiling_iff_77_by_86`) rules out both $22 \times 301$ and $43 \times 154$, leaving $77 \times 86$ (up to rotation) as the sole rectangle these 42 squares could possibly tile. Whether $77 \times 86$ admits a tiling remains open.

| Field | Summary |
| --- | --- |
| Problem | Erich Friedman Open Problem 10 (*Math Magic*, May 2005), $n = 21$, two copies of squares $1, \ldots, 21$ (area 6,622) |
| Status | Dimension reduction proved in Lean 4: rules out $22 \times 301$ and $43 \times 154$. Whether $77 \times 86$ can be tiled remains open. |
| Main theorems | `Squares42.exists_tiling_iff_77_by_86`, `Squares42.only_remaining_rectangle` ([Bridge.lean](Bridge.lean)); `Squares42.no_width_43` ([Width43.lean](Width43.lean)); `GuillotineSquares.no_guillotine_tiling` ([Guillotine.lean](Guillotine.lean)) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof for the dimension reduction in `Bridge`/`Squares`/`Width43`/`Projection`, and `native_decide` for the guillotine-tiling exclusion in `Guillotine.lean`) |
| Prior art | Checked 24 November 2026: Friedman's 22 November revision keeps the two-copy $n = 21$ case open; no earlier proof ruling out $43 \times 154$ was found (priority unconfirmed). |

## Proof overview

The formal model places all 42 squares on an integer grid and requires every unit cell of the $w \times h$ rectangle to be covered exactly once ([Squares.lean](Squares.lean)). Because $w \cdot h = 6{,}622 = 2 \cdot 7 \cdot 11 \cdot 43$ and every side must be at least $21$ to fit a $21 \times 21$ square, the only possible dimensions with $w \le h$ are $22 \times 301$, $43 \times 154$, and $77 \times 86$.

### Ruling out $22 \times 301$ ([Squares.lean](Squares.lean))

Placing a $21 \times 21$ square inside a strip of width 22 leaves a narrow $1 \times 21$ channel running along its side. Only $1 \times 1$ squares are thin enough to fit inside a channel of width 1, so filling it would require 21 unit squares—impossible when we only have two.

### Ruling out $43 \times 154$ ([Width43.lean](Width43.lean))

A tight row-counting argument forces the placement of the largest and smallest squares into a contradiction:

1. **Every row hits exactly three squares.** Each $k \times k$ square spans $k$ horizontal rows, so summed over all 42 squares the total number of `(row, square)` incidences is
   $$
   2 \sum_{k=1}^{21} k = 462 = 3 \times 154.
   $$
   On the other hand, even the two largest squares have combined width $21 + 21 = 42 < 43$, so every row of width 43 must intersect *at least* 3 squares. Since the average across the 154 rows equals the minimum of 3, every row hits **exactly** 3 squares.
2. **The two $21 \times 21$ squares overlap in 2 rows.** In any row containing a $1 \times 1$ square, the other two squares in that row must span the remaining width $43 - 1 = 42$, which forces both of them to be the two $21 \times 21$ squares (and prevents the two $1 \times 1$ squares from sharing a row, since $1 + 1 + 21 < 43$). Conversely, any row meeting both $21 \times 21$ squares leaves width $43 - 42 = 1$, forcing a $1 \times 1$ square. With two $1 \times 1$ squares available, the two $21 \times 21$ squares overlap in exactly 2 rows.
3. **Both $11 \times 11$ squares are demanded twice.** Outside that 2-row overlap, each $21 \times 21$ square protrudes into a disjoint 19-row strip on opposite sides of the overlap. Lean proves that each of these two 19-row strips needs both $11 \times 11$ squares, a contradiction.

### Ruling out guillotine tilings ([Guillotine.lean](Guillotine.lean))

Using `native_decide` over an exhaustive closed catalog of legal guillotine blocks, `GuillotineSquares.no_guillotine_tiling` also proves that no rectangle of any dimensions can be tiled by the 42 squares via recursive full horizontal/vertical cuts (`area_le_4104`, attained by a $36 \times 114$ sub-inventory rectangle).

## Reproduce

Run from this directory with Lean 4.36.0 (stdlib only; pure kernel proof for the dimension reduction, `native_decide` in [Guillotine.lean](Guillotine.lean)):

```sh
lake build
```

## References

- Erich Friedman, *Math Magic*: [Open Problem 10](https://erich-friedman.github.io/mathmagic/unsolved.html) and [results table (May 2005)](https://erich-friedman.github.io/mathmagic/0505.html)
- [Bridge.lean](Bridge.lean), [Squares.lean](Squares.lean), [Width43.lean](Width43.lean), [Projection.lean](Projection.lean), and [Guillotine.lean](Guillotine.lean)
