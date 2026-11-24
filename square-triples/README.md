# Two triples producing nine squares

Dujella asks whether six distinct positive integers can be split into two triples so that every product across the split is one less than a square. The unrestricted question remains open. [Dujella, Problem 1.4](https://web.math.pmf.unizg.hr/~duje/pdf/open2.pdf#page=2)

`SquareTriples.solution_ratio_1000` proves that in any solution, at least one triple’s largest entry exceeds 1,000 times its smallest. [Lean theorem](SquareTriples/Ratio.lean)

Order the triples as $a<b<c$ and $x<y<z$. Write $p=ax$ and $q=by$. The determinant of the nine square roots gives $64p^3(q+1)<cz$. If both triples span a factor of at most 1,000, then $cz\le 1{,}000{,}000p$. Cancelling $p$ forces $p<25$, since $q\ge p$ and $64\cdot25^2\cdot26=1{,}040{,}000$. [Determinant bound](SquareTriples/Determinant.lean)

Since $p+1$ is a square, $p$ is 3, 8, 15 or 24. For each possible smallest pair $a,x$, Lean enumerates the partners within the two ratio bounds. Its kernel checks that none completes all nine squares. [Finite check and ratio proof](SquareTriples/Ratio.lean)

Run the following commands in this directory with Lean 4.36.0.

```sh
lake build
lake env leanchecker SquareTriples.Determinant SquareTriples.Ratio
```
