# Can 42 squares tile a rectangle?

Take two squares of each side length from 1 through 21. Lean proves that
any rectangle they tile must measure **77 × 86**, up to rotation. Whether
they tile that rectangle remains open. Friedman lists this as the case
$n = 21$. [Open problem 10](https://erich-friedman.github.io/mathmagic/unsolved.html)

The formal model puts the squares on an integer grid and requires each unit
cell of the rectangle to be covered exactly once. The area is 6,622. Of the
three possible dimensions, a 22 × 301 rectangle would need 21 unit squares
beside a single 21-square. In a 43 × 154 rectangle, counting row intersections forces every
row to meet exactly three squares. The two unit squares then force the two
21-squares to overlap in exactly two rows. Each of the two 19-row strips on
opposite sides of that overlap requires both 11-squares. This gives the
contradiction. [Model and area argument](Squares.lean) · [Width-43 proof](Width43.lean)

The main theorem is `Squares42.exists_tiling_iff_77_by_86`. To check all six
modules with Lean 4.36.0, run `lake build` in this directory. [Main theorem](Bridge.lean)
