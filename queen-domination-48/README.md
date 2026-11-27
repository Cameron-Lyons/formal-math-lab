# Queen domination number of the 48 x 48 chessboard: gamma(Q_48) = 25

How many chess queens are needed on a $48 \times 48$ board so that every square is either occupied or attacked by a queen? Östergård and Weakley constructed a 25-queen dominating set ($\gamma(Q_{48}) \le 25$), and Davies (§9 of his 21 November 2026 preprint, `hexagonmath.org/pdf/2611.00830v1`) listed $n = 48$ as the next open even board.

The compiled Lean 4 program here (`lake exe queens48`) verifies Östergård and Weakley's 25-queen placement covering all 2,304 squares and exhaustively rules out 24 queens, giving $\gamma(Q_{48}) = 25$.

| Field | Summary |
| --- | --- |
| Problem | Queen domination number $\gamma(Q_{48})$ on the $48 \times 48$ board, Östergård and Weakley (2001), Davies (`hexagonmath.org/pdf/2611.00830v1`, §9) |
| Status | Solved ($\gamma(Q_{48}) = 25$). A compiled Lean search rules out 24 queens and verifies a 25-queen cover. |
| Entry point | `main` in [Main.lean](Main.lean) ([Local.lean](Local.lean), [Global.lean](Global.lean)) |
| Verification | `lake exe queens48` (Lean 4.36.0, stdlib only; compiled exhaustive enumeration rather than a kernel proof term, see argument below) |
| Prior art | Re-audited 26 November 2026: Aleksej Đukić published and certified $\gamma(Q_{48}) = 25$ on 22 November 2026 (OEIS A075458 rev. 125, `10.5281/zenodo.24537292`) using Davies' SAT frame method, two days before this folder. This program gives an independent non-SAT proof. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Proof that 24 queens cannot dominate the 48 x 48 board

A known placement of 25 queens covers all $48^2 = 2,304$ squares, and [Main.lean](Main.lean) checks those coordinates directly. It remains to rule out 24 queens.

### 1. Partition into nine 16 x 16 grids and count boundary squares

Color each square $(x, y) \in \{0, \ldots, 47\}^2$ by $(x \bmod 3, y \bmod 3)$. Each of the 9 color classes forms a $16 \times 16$ grid. Fix one grid and let $h$ be the number of queens inside it. Let $C, R, T, S$ count the queens in the four residue classes passing through that grid: columns ($x \bmod 3$), rows ($y \bmod 3$), difference diagonals ($(y - x) \bmod 3$), and sum diagonals ($(y + x) \bmod 3$). A queen inside the grid is counted 4 times, and every other queen is counted once. Hence:

$$
C + R + T + S = 24 + 3h.
$$

At least $e = 16 - C$ columns and $f = 16 - R$ rows of the grid are empty, and only diagonals can cover their $ef$ intersections. For $e, f \ge 2$, the outermost empty rows and columns form a boundary of $2e + 2f - 4$ intersections. Any diagonal hits that boundary at most twice, so $T + S \ge e + f - 2$. The same bound holds when $e = 1$ or $f = 1$, because each diagonal then covers at most one intersection.

Whenever $C, R < 16$, substituting gives $24 + 3h = C + R + T + S \ge (16 - e) + (16 - f) + (e + f - 2) = 30$, so $h \ge 2$: every such grid holds at least two queens. When $h = 2$, equality holds throughout: every available diagonal pairs two boundary intersections, those pairs partition the boundary, and all occupied lines in each of the four classes are distinct.

### 2. Enumerate the equality cases

Testing all weak compositions of 24 queens across the 9 grids leaves 3,012 distributions that satisfy the perimeter bound. For each 2-queen grid with $C, R < 16$, the program picks its empty rows and columns, takes the first unpaired boundary intersection, branches on its two diagonals (requiring each to match another unpaired boundary intersection), and checks that the resulting diagonals also cover every interior intersection. This tests 31 line-count shapes and leaves 21 surviving distributions ([Main.lean](Main.lean), [Local.lean](Local.lean)).

### 3. Fit the grids together globally

Two grids sharing a residue class of rows, columns, or diagonals must agree on which lines are occupied. Trying every compatible global combination across the 21 distributions splits into two cases ([Global.lean](Global.lean)):

* 12 distributions with a strip of three 2-queen grids: after transposing if needed, the strip fixes all occupied rows and both sets of occupied diagonals. A queen in row $y$ needs occupied diagonals $t = y - x$ and $s = y + x$ with $t + s = 2y$, and every combination leaves some occupied row without such a pair.
* 9 distributions with four 2-queen grids in a cross: these fix all 24 occupied columns and all 24 occupied rows. Whenever an uncovered square on an empty row and empty column has one diagonal unavailable, its other diagonal is forced. After propagation, each surviving combination fixes 23 or 24 distinct labels of each diagonal slope. At most one entry per slope is missing (counting multiplicity), and it is forced by $\sum t = \sum y - \sum x$ and $\sum s = \sum y + \sum x$. Every combination fails either those linear sums or the quadratic identity $\sum t^2 + \sum s^2 = 2\sum x^2 + 2\sum y^2$ (from $(y - x)^2 + (y + x)^2 = 2(x^2 + y^2)$).

Hence no 24-queen cover exists. Since any smaller cover could be enlarged to 24 queens, $\gamma(Q_{48}) = 25$.

## Run the verification

From this directory with the pinned Lean 4.36.0 toolchain (stdlib only):

```sh
lake exe queens48
```

The executable regenerates all data from the board size, checks the 25-queen placement on all 2,304 squares, and exhausts the 3,012 histograms, 31 local shapes, and 21 global configurations.

## References

* [Östergård and Weakley (2001), *Values of Domination Numbers of the Queen's Graph*, pp. 10-11](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v8i1r29/pdf/)
* [Davies (21 November 2026), §9 (`hexagonmath.org/pdf/2611.00830v1`)](https://hexagonmath.org/pdf/2611.00830v1#page=19)
* [Đukić (22 November 2026), OEIS A075458 certificate (`a075458_1.txt`)](https://oeis.org/A075458/a075458_1.txt) and [Zenodo preprint (`10.5281/zenodo.24537292`)](https://zenodo.org/records/24537292)
* [Prior-art audit](../PRIOR_ART.md)
