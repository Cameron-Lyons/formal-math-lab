# Dujella Problem 1.4: two triples producing nine squares

Can you split six distinct positive integers into two triples $\{a, b, c\}$ and $\{x, y, z\}$ so that every one of the nine cross-products plus one is a perfect square?

$$
ax + 1,\; ay + 1,\; az + 1,\; bx + 1,\; by + 1,\; bz + 1,\; cx + 1,\; cy + 1,\; cz + 1 \in \{k^2 : k \in \mathbb{Z}\}.
$$

This is Andrej Dujella's Problem 1.4 — also studied by Batta, Hajdu, and Pongrácz as the **$K_{3,3}$ bipartite Diophantine triple problem** (since the pairs $(u, v)$ whose shifted product $uv + 1$ must be a square form the edges of the complete bipartite graph $K_{3,3}$ between the two triples). Unrestricted existence of such six integers remains open.

The Lean 4 proof here (`SquareTriples.solution_ratio_1000`) proves that any solution must be dramatically stretched out: at least one of the two triples has its largest entry **strictly greater than $1{,}000$ times its smallest entry** ($c > 1000a$ or $z > 1000x$).

| Field | Summary |
| --- | --- |
| Problem | Dujella Problem 1.4, bipartite Diophantine triples ($K_{3,3}$ with $uv + 1 = \square$), Batta, Hajdu, and Pongrácz (`arXiv:2410.20120`, §6) |
| Status | Partial result (ratio lower bound $> 1000$). Unrestricted existence of six distinct positive integers remains open. |
| Main theorems | `SquareTriples.solution_ratio_1000`, `SquareTriples.ordered_solution_ratio_1000` in [SquareTriples/Ratio.lean](SquareTriples/Ratio.lean) |
| Verification | `lake build && lake env leanchecker SquareTriples.Determinant SquareTriples.Ratio` (Lean 4.36.0, stdlib only; pure kernel check) |
| Prior art | Checked 24 November 2026: the $3 + 3$ case is listed as open by Dujella and by Batta, Hajdu, and Pongrácz; priority of the factor-1000 bound is unverified. |

## How the proof works

Order the two triples as $0 < a < b < c$ and $0 < x < y < z$, and write $p = ax$ (the smallest cross-product) and $q = by$ (the middle cross-product).

**The big idea:** A $3 \times 3$ determinant inequality forces the largest cross-product $cz$ to grow at least quartically in $p$ and $q$. If *both* triples stayed within a factor of $1{,}000$, then $cz$ could be at most $1{,}000{,}000\, p$, which crushes $p$ below $25$. That leaves only four possible squares for $p + 1$, small enough for Lean's kernel to exhaust every remaining candidate directly.

1. **Determinant height bound ([SquareTriples/Determinant.lean](SquareTriples/Determinant.lean)):** Expanding the $3 \times 3$ determinant of the nine square roots $\sqrt{uv + 1}$ yields

   $$
   64 p^3 (q + 1) < cz.
   $$

2. **Crushing $p$ below $25$ ([SquareTriples/Ratio.lean](SquareTriples/Ratio.lean)):** Suppose for contradiction that both triples span a factor of at most $1{,}000$, meaning $c \le 1000a$ and $z \le 1000x$. Multiplying gives $cz \le 1{,}000{,}000\, ax = 1{,}000{,}000\, p$. Substituting into the determinant bound and dividing by $p > 0$ gives

   $$
   64 p^2 (q + 1) < 1{,}000{,}000.
   $$

   Since $q \ge p$, having $p \ge 25$ would imply $64 p^2 (q + 1) \ge 64 \cdot 25^2 \cdot 26 = 1{,}040{,}000$, a contradiction. Hence $p < 25$.

3. **Kernel-checked finite exhaustion ([SquareTriples/Ratio.lean](SquareTriples/Ratio.lean)):** Because $p + 1 = ax + 1$ must be a perfect square strictly between $1$ and $26$, we have $p + 1 \in \{4, 9, 16, 25\}$, so $p \in \{3, 8, 15, 24\}$. For every valid smallest pair $(a, x)$ with $ax \in \{3, 8, 15, 24\}$, Lean enumerates all candidate partners within the ratio and height bounds and checks with `decide +kernel` that none produces all nine squares.

## Reproduce

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
lake env leanchecker SquareTriples.Determinant SquareTriples.Ratio
```

## References

* [Andrej Dujella, *Open Problems*, Problem 1.4](https://web.math.pmf.unizg.hr/~duje/pdf/open2.pdf#page=2)
* [Batta, Hajdu, and Pongrácz, `arXiv:2410.20120v1`, §6](https://arxiv.org/html/2410.20120v1#S6)
