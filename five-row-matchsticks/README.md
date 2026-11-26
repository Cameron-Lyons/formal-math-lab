# Breaking every rectangle in a five-row matchstick grid

Form a grid of five rows and $n$ columns of unit squares, with one matchstick per unit edge. Let $S(n)$ be the fewest sticks whose removal breaks the outline of every positive-area, axis-aligned rectangle, including squares. Then

$$
S(1)=5,\qquad S(n)=\left\lfloor\frac{10n+4}{3}\right\rfloor\quad(n\ge 2).
$$

For example, 28 removals are necessary and sufficient on a $5\times 8$ grid. The Lean theorem `Matchsticks.five_row_matchstick_theorem` proves that the stated number is attained at every positive width and that every valid removal pattern costs at least that much. [Main theorem](Matchsticks.lean)

## Proof

A column scan tracks the 15 possible pairs of horizontal grid lines. A pair stays open while the two horizontal sides can still extend from an intact left side. Lean proves that the scan rejects a board exactly when four intact sides enclose a rectangle. [Geometric equivalence](Matchsticks/Geometry.lean)

A repeating six-column pattern attains the upper bound. For the lower bound, Lean checks a finite table of inequalities for extending a safe board by one column. Induction gives $3c\ge 10n+2$ for the number $c$ of removals at positive width, together with the sharper bound of five at width one. The kernel checks the table, the induction, and the construction using the Lean standard library. The main theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. [Construction](Matchsticks/Upper.lean) · [Lower bound](Matchsticks/Lower.lean) · [Certificate data](Matchsticks/Certificate.lean)

The two-page hand proof gives a geometric lower bound by showing how two L-shaped components would force an intact rectangle. [Illustrated proof (PDF)](matchstick-proof.pdf) · [Typst source](matchstick-proof.typ)

## Reproduce

Run these commands in this directory with Lean 4.36.0.

```sh
lake --wfail build
lake env leanchecker --fresh Matchsticks
```

Dreyer and Biedl introduced the rectangle-breaking problem in 1997. Niu and Tang reported five-row bounds differing by at most one in 2026. [Dreyer and Biedl, DIMACS 97-53](https://archive.dimacs.rutgers.edu/TechnicalReports/abstracts/1997/97-53.html) · [Niu and Tang, *Theoretical Computer Science*](https://doi.org/10.1016/j.tcs.2026.116199) · [Prior-art notes](../PRIOR_ART.md)
