# Tiling a rectangle with two copies of squares 1 through 21

Take 42 squares: two of each integer side length from 1 to 21, with total area $2 \sum_{k=1}^{21} k^2 = 6{,}622$. Erich Friedman's Math Magic Open Problem 10 asks for the minimum number of copies of each square $1 \times 1, \ldots, n \times n$ needed to tile a rectangle. The two-copy case at $n = 21$ is open.

The Lean 4 proof (`Squares42.exists_tiling_iff_77_by_86`) rules out both $22 \times 301$ and $43 \times 154$, leaving $77 \times 86$ (up to rotation) as the only rectangle these 42 squares could tile. Whether $77 \times 86$ can be tiled remains open.

| Field | Summary |
| --- | --- |
| Problem | Erich Friedman Open Problem 10 (*Math Magic*, May 2005), $n = 21$, two copies of squares $1, \ldots, 21$ (area 6,622) |
| Status | Dimension reduction proved in Lean 4: rules out $22 \times 301$ and $43 \times 154$. Whether $77 \times 86$ can be tiled remains open. |
| Main theorems | `Squares42.exists_tiling_iff_77_by_86`, `Squares42.only_remaining_rectangle` ([Bridge.lean](Bridge.lean)); `Squares42.no_width_43` ([Width43.lean](Width43.lean)) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof across all six modules) |
| Prior art | Checked 24 November 2026: Friedman's 22 November revision keeps the two-copy $n = 21$ case open; no earlier proof ruling out $43 \times 154$ was found (priority unconfirmed). See [PRIOR_ART.md](../PRIOR_ART.md#two-squares-of-each-side-from-1-through-21). |

## Proof overview

The formal model places all 42 squares on an integer grid and requires every unit cell of the $w \times h$ rectangle to be covered once ([Squares.lean](Squares.lean)). Because the total area is $6{,}622 = 2 \cdot 7 \cdot 11 \cdot 43$ and each side must be at least 21, the only possible dimensions (with $w \le h$) are $22 \times 301$, $43 \times 154$, and $77 \times 86$:

* Ruling out $22 \times 301$ ([Squares.lean](Squares.lean)): placing a $21 \times 21$ square inside width 22 leaves a $1 \times 21$ strip alongside it, which would need 21 unit squares when only two are available.
* Ruling out $43 \times 154$ ([Width43.lean](Width43.lean)): counting row intersections across the 154 rows forces every row to hit three squares. The two $1 \times 1$ squares then force the two $21 \times 21$ squares to overlap in 2 rows. Each of the two 19-row strips on opposite sides of that overlap then needs both $11 \times 11$ squares, a contradiction.

## Reproduce

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

## References

* Erich Friedman, Math Magic: [Open Problem 10](https://erich-friedman.github.io/mathmagic/unsolved.html) and [results table (May 2005)](https://erich-friedman.github.io/mathmagic/0505.html)
* [Bridge.lean](Bridge.lean), [Squares.lean](Squares.lean), and [Width43.lean](Width43.lean)
* [Prior-art audit](../PRIOR_ART.md#two-squares-of-each-side-from-1-through-21)
