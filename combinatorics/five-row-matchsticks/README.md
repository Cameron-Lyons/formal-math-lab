# Breaking every rectangle in a five-row matchstick grid

Build a grid of 5 rows and $n$ columns of unit squares using one matchstick for every unit edge. How few matchsticks must you remove so that **no** intact axis-aligned rectangle of positive area remains anywhere in the grid—not just $1 \times 1$ squares, but also $2 \times 3$, $5 \times 1$, or any other $a \times b$ rectangle formed by surviving matchsticks?

Let $S(n)$ be that minimum number of removals. This Lean 4 development proves the exact formula for every positive width $n$:

$$
S(1) = 5, \qquad S(n) = \left\lfloor \frac{10n + 4}{3} \right\rfloor \quad (n \ge 2).
$$

For example, $S(2) = 8$, $S(3) = 11$, and on a $5 \times 8$ grid exactly $\lfloor 84/3 \rfloor = 28$ removals are both necessary and sufficient. The main theorem `Matchsticks.five_row_matchstick_theorem` ([Main theorem](Matchsticks.lean)) proves that this exact bound is achieved at every $n \ge 1$ and cannot be beaten by any valid removal pattern.

| Field | Summary |
| --- | --- |
| Problem | Minimum matchstick removals $S(n)$ breaking every axis-aligned rectangle in a $5 \times n$ grid (Dreyer and Biedl, 1997; Niu and Tang, 2026) |
| Result | Exact formula $S(1) = 5$ and $S(n) = \lfloor (10n + 4)/3 \rfloor$ for all $n \ge 2$ |
| Main theorem | `Matchsticks.five_row_matchstick_theorem` in [Matchsticks.lean](Matchsticks.lean) |
| Verification | `lake --wfail build && lake env leanchecker --fresh Matchsticks` (Lean 4.36.0, `Init` prelude only; pure kernel proof using only `propext`, `Classical.choice`, `Quot.sound`) |

## Proof strategy

### Lower bound: the dual-graph argument

**The big idea.** Translate matchstick removals into a graph whose vertices are the rooms of the grid rather than the corners. Place one vertex inside each of the $5n$ unit squares, plus one extra **exterior vertex** representing the infinite region outside the grid. Whenever you remove a matchstick, think of opening a doorway between the two regions it separates—so add an edge joining their two vertices in this **dual graph**.

Why does this help? A connected component of the dual graph is a cluster of unit squares linked by removed matchsticks and sealed off by an unbroken wall of surviving matchsticks. More generally, **any union of interior components** (components not containing the exterior vertex) has a completely intact outer boundary—so no such union can form a rectangle!

That single geometric fact gives the whole lower bound:

1. **At least one cell joins the exterior.** The union of all $5n$ cells is the entire $5 \times n$ rectangle, so it cannot consist solely of interior components. Thus the exterior component contains $c_0 \ge 1$ grid cells (plus the exterior vertex itself, so $c_0 + 1$ vertices and at least $c_0$ edges).
2. **Width $n = 1$:** Any connected group of cells in a single column is a $k \times 1$ rectangle, so no interior components are allowed at all. Every cell must connect to the exterior, forcing $e \ge 5$ removals ($S(1) = 5$).
3. **Every interior component at width $n \ge 2$ has at least 3 cells.** A 1-cell component is an intact $1 \times 1$ square, and a 2-cell component is an intact $1 \times 2$ or $2 \times 1$ rectangle. Suppose there are $m$ interior components of sizes $c_1, \ldots, c_m \ge 3$. Each needs at least $c_i - 1$ edges (spanning tree), so the total number of removed sticks $e$ satisfies
   $$
   e \ge c_0 + \sum_{i=1}^m (c_i - 1) = 5n - m.
   $$
   Since $3m \le \sum_{i=1}^m c_i = 5n - c_0 \le 5n - 1$, multiplying by 3 gives
   $$
   3e \ge 15n - 3m \ge 10n + 1.
   $$
   When $n \equiv 0$ or $1 \pmod 3$, $\lceil (10n + 1)/3 \rceil$ already equals $\lfloor (10n + 4)/3 \rfloor$.
4. **The extra stick when $n = 3k + 2$.** Here $3e \ge 10n + 1 = 3(10k + 7)$ only gives $e \ge 10k + 7$, one shy of $\lfloor (10n + 4)/3 \rfloor = 10k + 8$. Achieving equality $e = 10k + 7$ forces zero slack everywhere: $c_0 = 1$ (only one cell joins the exterior) and every interior component has size exactly 3. Because straight $1 \times 3$ and $3 \times 1$ trominoes are rectangles, every interior component must be an **L-tromino**. Pick an end column (left or right) that avoids the single exterior cell. That column has 5 cells (an odd number), and each L-tromino covers either 1 or 2 cells of an end column; by parity, some L-tromino covers just 1 cell of that end column, which forces an adjacent L-tromino to pair with it into an intact $3 \times 2$ rectangle—contradiction!

Lean formalizes this entire dual-graph proof directly, with no lookup certificates or search tables ([Lower bound](Matchsticks/Lower.lean)).

### Upper bound: periodic construction and 15-bit column scan

To show that $\lfloor (10n + 4)/3 \rfloor$ removals always suffice for $n \ge 2$ (and $5$ for $n = 1$), start with two initial columns and then repeat a three-column block alternating with its top-to-bottom reflection.

To verify that no rectangle survives at *any* width $n$, Lean uses a **15-bit column scan**. Why 15 bits? A 5-row grid has 6 horizontal grid lines, giving $\binom{6}{2} = 15$ pairs of horizontal lines that could act as the top and bottom edges of a rectangle. Sweeping left to right across columns, one bit per pair tracks whether those two lines are currently "open" (joined by an unbroken left vertical side with unbroken top and bottom segments reaching the current column). A surviving vertical segment closing an open pair would complete an intact rectangle. Lean proves that any board accepted by the scan is rectangle-free and checks the repeating six-column period directly in the kernel ([Construction](Matchsticks/Upper.lean) · [Scan soundness](Matchsticks/Geometry.lean)).

## Verification and trust boundary

The package depends only on Lean's built-in `Init` prelude (no Mathlib, no `native_decide`, no external tools), and `Matchsticks.five_row_matchstick_theorem` uses only Lean's three standard axioms (`propext`, `Classical.choice`, and `Quot.sound`).

Run these commands in this directory with Lean 4.36.0:

```sh
lake --wfail build
lake env leanchecker --fresh Matchsticks
```

## References

Dreyer and Biedl introduced the rectangle-breaking problem in 1997; Niu and Tang reported five-row bounds differing by at most one in 2026.

- [Dreyer and Biedl, DIMACS 97-53](https://archive.dimacs.rutgers.edu/TechnicalReports/abstracts/1997/97-53.html)
- [Niu and Tang, *Theoretical Computer Science*](https://doi.org/10.1016/j.tcs.2026.116199)
