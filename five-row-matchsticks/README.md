# Breaking every rectangle in a five-row matchstick grid

Form a grid of five rows and $n$ columns of unit squares, with one matchstick per unit edge. Let $S(n)$ be the fewest sticks whose removal breaks the outline of every positive-area, axis-aligned rectangle, including squares. Then

$$
S(1)=5,\qquad S(n)=\left\lfloor\frac{10n+4}{3}\right\rfloor\quad(n\ge 2).
$$

For example, 28 removals are necessary and sufficient on a $5\times 8$ grid. The Lean theorem `Matchsticks.five_row_matchstick_theorem` proves that the stated number is attained at every positive width and that every valid removal pattern costs at least that much. [Main theorem](Matchsticks.lean)

## Proof

**Lower bound.** Form the dual graph on the $5n$ unit cells plus one exterior vertex, adding an edge for each erased stick. Any union of components disjoint from the exterior has an intact boundary and therefore cannot be a rectangle. Consequently at least one cell joins the exterior, width $1$ admits no interior component, and every interior component at width $n\ge 2$ has at least $3$ cells, giving $3e\ge 10n+1$. When $n=3k+2$, equality forces one exterior cell and all interior components to be L-trominoes; on an end column avoiding the exterior cell, parity gives an L covering a single cell of that column, which forces an adjacent L to pair with it into an intact $3\times 2$ rectangle. Lean formalizes this dual-graph argument directly with no lookup certificate or search table. [Lower bound](Matchsticks/Lower.lean) · [Illustrated proof (PDF)](matchstick-proof.pdf) · [Typst source](matchstick-proof.typ)

**Upper bound.** Two starting columns followed by an alternating three-column block and its top-to-bottom reflection attain the bound for every $n\ge 1$. A 15-bit column scan tracks open pairs of horizontal lines; Lean proves that a scan-accepted board has no intact rectangle and checks the repeating six-column period directly in the kernel. [Construction](Matchsticks/Upper.lean) · [Scan soundness](Matchsticks/Geometry.lean)

The package uses only Lean's built-in `Init` prelude, and the main theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce

Run these commands in this directory with Lean 4.36.0.

```sh
lake --wfail build
lake env leanchecker --fresh Matchsticks
```

Dreyer and Biedl introduced the rectangle-breaking problem in 1997. Niu and Tang reported five-row bounds differing by at most one in 2026. [Dreyer and Biedl, DIMACS 97-53](https://archive.dimacs.rutgers.edu/TechnicalReports/abstracts/1997/97-53.html) · [Niu and Tang, *Theoretical Computer Science*](https://doi.org/10.1016/j.tcs.2026.116199) · [Prior-art notes](../PRIOR_ART.md)
