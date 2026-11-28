# No-three-in-line problem on the $75 \times 75$ grid

How many points can you place on an $n \times n$ integer grid $\{0, 1, \ldots, n - 1\}^2$ so that **no three points lie on the same straight line** (horizontal, vertical, diagonal, or any slanted rational slope)? By the pigeonhole principle, each of the $n$ rows can hold at most 2 points, giving an immediate ceiling of $2n$ points.

Achim Flammenkamp's record table lists full $2n$-point solutions for $n = 74, 76, 78$, but leaves $n = 75$ blank. Dropping Thomas Prellberg's 148-point solution for $74 \times 74$ straight onto the $75 \times 75$ grid gives $148 \le \max \le 150$, while whether 149 or 150 points fit remains open.

The Lean 4 proofs here formally verify Prellberg's 148-point placement and establish several sharp obstructions for any hypothetical 150-point solution: none can extend Prellberg's set (or even repair a 32-row window of it), none can have 90° rotational symmetry, and standard modular polynomial curves modulo 75 fall far short (at most 50 points per curve).

| Field | Summary |
| --- | --- |
| Problem | No-three-in-line problem on the $75 \times 75$ grid ($n = 75$, 148 vs. 150 points), Prellberg's 148-point $74 \times 74$ configuration, Flammenkamp's table |
| Status | Partial results ($148 \le \max \le 150$ and obstructions). Whether 149 or 150 points can be placed remains open. |
| Main theorems | `Grid75.bounds` ([Grid75Results.lean](Grid75Results.lean)), `Grid75.maximum_in_range`, `witness_cannot_extend`, `no_quarterTurn_150` ([Grid75.lean](Grid75.lean)), `omitted_rows_separated` / `no_32_row_repair` ([StripBounds.lean](StripBounds.lean)), `achievable_150_of_halfTurn_extension` ([HalfTurn.lean](HalfTurn.lean)), `ModularCurve.CRT.one_curve_bound_50` / `two_curves_bound_100` ([PolynomialCRT.lean](PolynomialCRT.lean)) |
| Verification | `lake build Grid75` (bounds only) or `lake build` (all theorems; Lean 4.36.0, stdlib only) |
| Prior art | Checked 23 November 2026: the 148-point configuration is Prellberg's 20 July 2026 $74 \times 74$ solution; Flammenkamp's 28 October table leaves $n = 75$ blank. |

## Lean results

Three grid points $(x_1, y_1), (x_2, y_2), (x_3, y_3)$ are collinear if and only if the area determinant $(x_2 - x_1)(y_3 - y_1) - (y_2 - y_1)(x_3 - x_1)$ vanishes. Using this exact integer test, Lean establishes the following theorems:

| Lean declaration (namespace `Grid75`) | File | Result |
| --- | --- | --- |
| `bounds`, `maximum_in_range` | [Grid75Results.lean](Grid75Results.lean), [Grid75.lean](Grid75.lean) | The maximum number of non-collinear points on $\{0, \ldots, 74\}^2$ is 148, 149, or 150: at most 2 points per row gives $\le 150$, while Prellberg's 148 points are verified distinct with every triple having nonzero determinant. |
| `witness_cannot_extend` | [Grid75.lean](Grid75.lean) | Prellberg's 148-point placement is maximal: no single 149th point can be added anywhere on the $75 \times 75$ grid without creating a collinear triple. |
| `omitted_rows_separated`, `no_32_row_repair` | [StripBounds.lean](StripBounds.lean) | Local edits cannot fix Prellberg's placement into a 150-point solution: every 150-point configuration must discard at least two of Prellberg's 148 points whose row indices differ by at least 32 (so no repair confined to any 32-row horizontal band works). |
| `no_quarterTurn_150` | [Grid75.lean](Grid75.lean) | No 150-point configuration on the $75 \times 75$ grid is invariant under 90° rotation. (Intuitively, on an odd grid, 90° rotation splits the board into 4-point orbits plus the single center point, forcing any invariant subset to have size $\equiv 0$ or $1 \pmod 4$, whereas $150 \equiv 2 \pmod 4$.) |
| `achievable_150_of_halfTurn_extension` | [HalfTurn.lean](HalfTurn.lean) | Conversely, 180° (half-turn) symmetry gives a free upgrade: any valid 149-point extension of a half-turn invariant 148-point set can also include the 149th point's 180° opposite (antipode), producing a valid 150-point solution. |
| `ModularCurve.CRT.one_curve_bound_50`, `two_curves_bound_100` | [PolynomialCRT.lean](PolynomialCRT.lean) | Algebraic constructions using polynomial curves modulo $75 = 3 \cdot 5^2$ cannot reach 150: any single polynomial parametrization modulo 75 contributes at most 50 points in general position, and two such curves contribute at most 100. |

## Reproduce

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
# Bounds 148..150 and basic witness checks only
lake build Grid75

# Full suite (symmetry, polynomial curve bounds, and 32-row strip certificates)
lake build
```

## References

- Achim Flammenkamp's No-Three-in-Line [table](https://wwwhomes.uni-bielefeld.de/achim/no3in/table.html), [discovery notes](https://wwwhomes.uni-bielefeld.de/achim/no3in/readme.html#C), and [Prellberg's $74 \times 74$ data (`n74_rot4.few`)](https://wwwhomes.uni-bielefeld.de/achim/no3in/download/configurations/n74_rot4.few)
