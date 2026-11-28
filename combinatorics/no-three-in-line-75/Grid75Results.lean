import HalfTurn
import PolynomialCRT
import StripBounds

/-!
# How many points fit on the 75 × 75 grid?

At most two selected points can lie in each row. There are 75 rows, so the
upper bound is 150. For the lower bound, Prellberg's 148 points already lie
in the first 74 rows and columns. Lean checks that they are distinct and
that no three are collinear.

The maximum is therefore either 148, 149, or 150.
Whether `Grid75.Achievable 150` holds remains unresolved here.

Run `lake build Grid75` to check these two arguments, or `lake build` for
the additional results about symmetry, polynomial constructions, and row changes.
-/

/-- The verified lower and upper bounds for the unrestricted problem. -/
theorem Grid75.bounds :
    Grid75.Achievable 148 ∧ ∀ k, Grid75.Achievable k → k ≤ 150 :=
  ⟨Grid75.lower_bound, fun _ => Grid75.upper_bound⟩
