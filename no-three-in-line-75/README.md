# No three in line on a 75 × 75 grid

How many points can be chosen from `{0, …, 74}²` with no three on a straight line?
Lean proves that the maximum is between **148 and 150**, inclusive.
Whether a placement of 150 exists remains unresolved here. [Lean theorem `Grid75.bounds`](Grid75Results.lean)

At most two points can lie in each of the 75 rows, giving the upper bound.
For the lower bound, Thomas Prellberg’s 148-point placement on the 74 × 74 grid also fits
on this grid. Lean checks that the points are distinct and that every triple has
nonzero determinant. [Coordinates and proof](Grid75.lean) · [Flammenkamp’s configuration table](https://wwwhomes.uni-bielefeld.de/achim/no3in/table.html) · [Original 74 × 74 configurations](https://wwwhomes.uni-bielefeld.de/achim/no3in/download/configurations/n74_rot4.few)

Run `lake build Grid75` in this directory to verify the two bounds, or `lake build`
to also check the results about symmetry, polynomial constructions, and changes to the 148-point placement.
