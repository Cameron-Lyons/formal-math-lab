# Box-free 2-colorings of the $6 \times 7 \times n$ grid

Color every integer point of a 3D grid of size $6 \times 7 \times n$ either red or blue. The coloring is **box-free** if no axis-aligned rectangular box $\{x_1, x_2\} \times \{y_1, y_2\} \times \{z_1, z_2\}$ ($x_1 < x_2$, $y_1 < y_2$, $z_1 < z_2$) has all 8 of its corners the same color. Equivalently, if you slice the grid into $n$ horizontal $6 \times 7$ layers, a coloring is box-free if and only if no two layers share an identical monochromatic $2 \times 2$ rectangle (same pair of rows, same pair of columns, and same color).

Genkin (`10.5281/zenodo.24457907`, Theorem 5.1 and Question 8.1) built a 50-layer box-free coloring of $6 \times 7 \times 50$, proved that $n \le 52$, and asked whether height 52 can actually be reached. The Lean 4 proof here settles Question 8.1 completely: it constructs an explicit 52-layer box-free coloring and formally proves the matching upper bound $n \le 52$, establishing `BoxFree.exists_boxFree_iff`—a box-free 2-coloring of $6 \times 7 \times n$ exists if and only if $n \le 52$.

| Field | Summary |
| --- | --- |
| Problem | Box-free 2-coloring of $6 \times 7 \times n$, Genkin Question 8.1 (`10.5281/zenodo.24457907`), exact maximum height $n = 52$ |
| Status | Solved in Lean 4 ($n = 52$, improving Genkin's 50-layer coloring to match the upper bound). |
| Main theorem | `BoxFree.exists_boxFree_iff (n : Nat) : (∃ C : Coloring n, BoxFree C) ↔ n ≤ 52` in [BoxFree.lean](BoxFree.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel check) |
| Prior art | Checked 24 November 2026: Genkin v2 built 50 layers, proved the upper bound 52, and asked in Question 8.1 whether 52 is possible. |

## Proof overview

Because a monochromatic 3D box is simply a colored $2 \times 2$ rectangle repeated in two different layers, the problem becomes packing as many $6 \times 7$ layers as possible without reusing any colored rectangle:

- **Lower bound ($n = 52$, [BoxFree/Construction.lean](BoxFree/Construction.lean)):** The 52-layer coloring is given explicitly, one layer per line, as six rows of seven bits. Lean's kernel checks directly that all colored monochromatic $2 \times 2$ rectangles across the 52 layers are pairwise distinct, so no monochromatic box exists.
- **Upper bound ($n \le 52$, [BoxFree/LayerBound.lean](BoxFree/LayerBound.lean), [BoxFree/Upper.lean](BoxFree/Upper.lean)):**
  1. **Total rectangle budget:** A $6 \times 7$ layer contains $\binom{6}{2} = 15$ row pairs and $\binom{7}{2} = 21$ column pairs, giving $2 \cdot \binom{6}{2}\binom{7}{2} = 630$ possible colored rectangles in total.
  2. **Minimum cost per layer:** In any 2-coloring of a 6-cell column, the color split is $(6, 0)$, $(5, 1)$, $(4, 2)$, or $(3, 3)$, producing at least $\binom{3}{2} + \binom{3}{2} = 6$ same-color row pairs. Across 7 columns that gives at least $7 \cdot 6 = 42$ occurrences distributed among $2 \cdot \binom{6}{2} = 30$ possible `(row pair, color)` types. Since $e$ occurrences of one type create $\binom{e}{2} \ge e - 1$ rectangles, Lean proves every 2-coloring of $6 \times 7$ contains at least $42 - 30 = 12$ monochromatic rectangles.
  3. **Pigeonhole contradiction:** Fifty-three layers would use at least $53 \cdot 12 = 636 > 630$ monochromatic rectangles, forcing a repeated rectangle and therefore a monochromatic 3D box. (By contrast, 52 layers spend at least $52 \cdot 12 = 624$ of the 630 available rectangles—leaving a slack of at most 6 rectangles across the entire stack!)

## Reproduce

Run from this directory with Lean 4.36.0 (stdlib only; pure kernel verification, no `native_decide`):

```sh
lake build
```

## References

- [Genkin, Theorem 5.1 and Question 8.1 (`10.5281/zenodo.24457907`)](https://zenodo.org/records/24457907)
- [BoxFree.lean](BoxFree.lean) and [BoxFree/Construction.lean](BoxFree/Construction.lean)
