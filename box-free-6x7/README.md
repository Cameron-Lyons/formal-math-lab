# Box-free 2-colorings of the 6 x 7 x n grid

A 2-coloring of the 3D integer grid $6 \times 7 \times n$ is *box-free* if no axis-aligned box $\{x_1, x_2\} \times \{y_1, y_2\} \times \{z_1, z_2\}$ has all 8 corners the same color. Genkin (`10.5281/zenodo.24457907`, Theorem 5.1 and Question 8.1) built a box-free $6 \times 7 \times 50$ coloring, proved $n \le 52$, and asked whether height 52 can be reached.

The Lean 4 proof here settles Question 8.1. It gives a 52-layer box-free coloring of $6 \times 7 \times 52$ and proves the matching bound $n \le 52$. The main theorem `BoxFree.exists_boxFree_iff` shows that a box-free 2-coloring of $6 \times 7 \times n$ exists if and only if $n \le 52$.

| Field | Summary |
| --- | --- |
| Problem | Box-free 2-coloring of $6 \times 7 \times n$, Genkin Question 8.1 (`10.5281/zenodo.24457907`), exact maximum height $n = 52$ |
| Status | Solved in Lean 4 ($n = 52$, improving Genkin's 50-layer coloring to match the upper bound). |
| Main theorem | `BoxFree.exists_boxFree_iff (n : Nat) : (∃ C : Coloring n, BoxFree C) ↔ n ≤ 52` in [BoxFree.lean](BoxFree.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel check) |
| Prior art | Checked 24 November 2026: Genkin v2 built 50 layers, proved the upper bound 52, and asked in Question 8.1 whether 52 is possible. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Proof overview

* Lower bound ($n = 52$, [BoxFree/Construction.lean](BoxFree/Construction.lean)): the 52-layer coloring is written one layer per line as six rows of seven bits. A monochromatic box occurs if and only if two distinct layers share a monochromatic $2 \times 2$ rectangle (same row pair, column pair, and color). Lean's kernel checks that no colored rectangle repeats across the 52 layers.
* Upper bound ($n \le 52$, [BoxFree/LayerBound.lean](BoxFree/LayerBound.lean), [BoxFree/Upper.lean](BoxFree/Upper.lean)): a $6 \times 7$ layer has $2 \cdot \binom{6}{2}\binom{7}{2} = 630$ possible colored rectangles. Lean proves every 2-coloring of $6 \times 7$ contains at least 12 monochromatic rectangles. Since $53 \cdot 12 = 636 > 630$, any 53 layers force a repeated rectangle and thus a monochromatic box.

## Reproduce

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

## References

* [Genkin, Theorem 5.1 and Question 8.1 (`10.5281/zenodo.24457907`)](https://zenodo.org/records/24457907)
* [BoxFree.lean](BoxFree.lean) and [BoxFree/Construction.lean](BoxFree/Construction.lean)
* [Prior-art audit](../PRIOR_ART.md)
