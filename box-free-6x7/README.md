# Box-free 2-colorings of the 6 x 7 x n grid: exact maximum height n = 52 (Genkin Question 8.1) — Lean 4 proof

**Solved — exact maximum proved in Lean 4: $n = 52$.** A red–blue (2-)coloring of the 3D integer grid $6 \times 7 \times n$ is *box-free* if it contains no monochromatic axis-aligned box $\{x_1, x_2\} \times \{y_1, y_2\} \times \{z_1, z_2\}$ (all 8 corners the same color). Genkin (`10.5281/zenodo.24457907`, Theorem 5.1 and Question 8.1) constructed a box-free $6 \times 7 \times 50$ coloring, proved the upper bound $n \le 52$, and asked whether height 52 is attainable.

This Lean 4 project answers **Question 8.1 affirmatively**: it exhibits an explicit **52-layer** box-free coloring of $6 \times 7 \times 52$ and proves the matching upper bound $n \le 52$, establishing `BoxFree.exists_boxFree_iff`: a box-free 2-coloring of $6 \times 7 \times n$ exists **if and only if $n \le 52$**.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Box-free 2-coloring of the $6 \times 7 \times n$ grid** (monochromatic rectangular box / 8-corner cube avoidance), **Genkin Question 8.1** (`10.5281/zenodo.24457907`), exact maximum height `n = 52` (`6x7x52`) |
| **Status** | **Solved in Lean 4.** Exact maximum height is **52** (improving Genkin's 50-layer construction to match the upper bound 52). |
| **Main Lean theorem** | `BoxFree.exists_boxFree_iff (n : Nat) : (∃ C : Coloring n, BoxFree C) ↔ n ≤ 52` in [BoxFree.lean](BoxFree.lean) |
| **Verification** | `lake build` (Lean 4.36.0, stdlib only; pure kernel check) |
| **Prior-art status** | Checked **24 November 2026**: Genkin v2 constructed 50 layers, proved the upper bound 52, and posed attainability of 52 as Question 8.1. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Proof overview

* **Lower bound ($n = 52$ construction, [BoxFree/Construction.lean](BoxFree/Construction.lean)):** the explicit 52-layer coloring is written one layer per line as six rows of seven bits. A monochromatic box occurs if and only if two distinct layers contain the same monochromatic $2 \times 2$ rectangle (same row pair, column pair, and color). Lean's kernel checks that no colored rectangle repeats across the 52 layers.
* **Upper bound ($n \le 52$, [BoxFree/LayerBound.lean](BoxFree/LayerBound.lean), [BoxFree/Upper.lean](BoxFree/Upper.lean)):** there are $2 \cdot \binom{6}{2}\binom{7}{2} = 630$ possible colored rectangles in a $6 \times 7$ layer. Lean proves every 2-coloring of $6 \times 7$ contains at least 12 monochromatic rectangles; since $53 \cdot 12 = 636 > 630$, any 53 layers force a repeated rectangle and hence a monochromatic box.

## Reproduce

Run from this directory with Lean **4.36.0** (standard library only):

```sh
lake build
```

## References

* [Genkin, Theorem 5.1 and Question 8.1 (`10.5281/zenodo.24457907`)](https://zenodo.org/records/24457907)
* [Exact-height theorem](BoxFree.lean) · [52-layer coloring](BoxFree/Construction.lean)
* [Dated prior-art audit](../PRIOR_ART.md)
