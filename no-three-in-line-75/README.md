# No-three-in-line problem on the 75 x 75 grid

The no-three-in-line problem asks for the largest subset of $\{0, 1, \ldots, n - 1\}^2$ with no three points collinear. Achim Flammenkamp's table records full $2n$-point configurations for $n = 74, 76, 78$ and leaves $n = 75$ blank. Whether 149 or 150 points fit on the $75 \times 75$ grid remains open.

The Lean 4 proofs here verify Thomas Prellberg's 148-point placement on $\{0, \ldots, 74\}^2$ (giving $148 \le \max \le 150$) and prove several obstructions for any 150-point solution: no 150-point solution extends Prellberg's 148-point set or repairs a 32-row window of it, no 150-point solution has 90° rotational symmetry, and polynomial curves modulo 75 contribute at most 50 points each.

| Field | Summary |
| --- | --- |
| Problem | No-three-in-line problem on the $75 \times 75$ grid ($n = 75$, 148 vs. 150 points), Prellberg's 148-point $74 \times 74$ configuration, Flammenkamp's table |
| Status | Partial results ($148 \le \max \le 150$ and obstructions). Whether 149 or 150 points can be placed remains open. |
| Main theorems | `Grid75.bounds` ([Grid75Results.lean](Grid75Results.lean)), `Grid75.maximum_in_range`, `witness_cannot_extend`, `no_quarterTurn_150` ([Grid75.lean](Grid75.lean)), `omitted_rows_separated` / `no_32_row_repair` ([StripBounds.lean](StripBounds.lean)), `achievable_150_of_halfTurn_extension` ([HalfTurn.lean](HalfTurn.lean)), `ModularCurve.CRT.one_curve_bound_50` / `two_curves_bound_100` ([PolynomialCRT.lean](PolynomialCRT.lean)) |
| Verification | `lake build Grid75` (bounds only) or `lake build` (all theorems; Lean 4.36.0, stdlib only) |
| Prior art | Checked 23 November 2026: the 148-point configuration is Prellberg's 20 July 2026 $74 \times 74$ solution; Flammenkamp's 28 October table leaves $n = 75$ blank. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Lean results

| Lean declaration (namespace `Grid75`) | File | Result |
| --- | --- | --- |
| `bounds`, `maximum_in_range` | [Grid75Results.lean](Grid75Results.lean), [Grid75.lean](Grid75.lean) | The maximum number of non-collinear points on $\{0, \ldots, 74\}^2$ is 148, 149, or 150 (at most 2 per row gives $\le 150$; Prellberg's 148 points are checked distinct with every triple having nonzero determinant). |
| `witness_cannot_extend` | [Grid75.lean](Grid75.lean) | Prellberg's 148-point placement cannot be extended by any single 149th point on the $75 \times 75$ grid. |
| `omitted_rows_separated`, `no_32_row_repair` | [StripBounds.lean](StripBounds.lean) | Every 150-point solution must omit at least two points of Prellberg's 148-point placement whose row indices differ by at least 32 (no repair confined to a 32-row band succeeds). |
| `no_quarterTurn_150` | [Grid75.lean](Grid75.lean) | No 150-point configuration on the $75 \times 75$ grid is invariant under 90° rotation. |
| `achievable_150_of_halfTurn_extension` | [HalfTurn.lean](HalfTurn.lean) | Any valid 149-point extension of a half-turn (180°) invariant 148-point set extends via its antipode to a valid 150-point solution. |
| `ModularCurve.CRT.one_curve_bound_50`, `two_curves_bound_100` | [PolynomialCRT.lean](PolynomialCRT.lean) | Any polynomial parametrization modulo 75 contributes at most 50 points in general position (and two such curves contribute at most 100). |

## Reproduce

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
# Bounds 148..150 and basic witness checks only
lake build Grid75

# Full suite (symmetry, polynomial curve bounds, and 32-row strip certificates)
lake build
```

## References

* Achim Flammenkamp's No-Three-in-Line [table](https://wwwhomes.uni-bielefeld.de/achim/no3in/table.html), [discovery notes](https://wwwhomes.uni-bielefeld.de/achim/no3in/readme.html#C), and [Prellberg's $74 \times 74$ data (`n74_rot4.few`)](https://wwwhomes.uni-bielefeld.de/achim/no3in/download/configurations/n74_rot4.few)
* [Prior-art audit](../PRIOR_ART.md)
