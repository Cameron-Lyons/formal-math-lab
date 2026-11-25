# Queen domination number of the 48 x 48 chessboard: gamma(Q_48) = 25 — Lean 4 verification and exhaustive exclusion of 24

**Solved: the queen domination number of the $48 \times 48$ board is $\gamma(Q_{48}) = 25$.** What is the minimum number of chess queens needed on a $48 \times 48$ chessboard so that every square is either occupied by or attacked by at least one queen? Östergård and Weakley constructed a 25-queen dominating set ($\gamma(Q_{48}) \le 25$), and Davies (§9 of his 21 November 2026 preprint, `hexagonmath.org/pdf/2611.00830v1`) identified $n = 48$ as the next open even board.

This Lean 4 project verifies Östergård and Weakley's explicit 25-queen placement covering all 2,304 squares and proves by compiled exhaustive enumeration (`lake exe queens48`) that **no 24-queen dominating set exists**, establishing $\gamma(Q_{48}) = 25$.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Queen domination number** on the **48 × 48 chessboard**, `gamma(Q_48) = 25` ($\gamma(Q_{48}) = 25$), domination number of the queen's graph $Q_{48}$, Östergård–Weakley (`Ostergard–Weakley`, 2001), Davies (`hexagonmath.org/pdf/2611.00830v1`, §9) |
| **Status** | **Solved ($\gamma(Q_{48}) = 25$).** Compiled Lean enumeration excludes 24 queens and verifies a 25-queen cover. |
| **Entry point** | `main` in [Main.lean](Main.lean) (`Local.lean`, `Global.lean`) |
| **Verification** | `lake exe queens48` (Lean 4.35.0, stdlib only; compiled exhaustive enumeration — not a kernel proof term, see argument below for completeness) |
| **Prior-art status** | Checked **24 November 2026**: Östergård–Weakley give the 25-queen upper bound; Davies listed $48 \times 48$ as open on 21 November 2026. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Proof that 24 queens cannot dominate the 48 × 48 board

A known placement of 25 queens covers all $48^2 = 2,304$ squares; [Main.lean](Main.lean) verifies those coordinates directly. It remains to rule out 24 queens.

### 1. Partition into nine 16 × 16 grids and count boundary squares

Color each square $(x, y) \in \{0, \ldots, 47\}^2$ by $(x \bmod 3, y \bmod 3)$. Each of the 9 color classes forms a $16 \times 16$ grid. Fix one grid and let $h$ be the number of queens inside it. Let $C, R, T, S$ count the queens in the four residue classes passing through that grid: columns ($x \bmod 3$), rows ($y \bmod 3$), difference diagonals ($(y - x) \bmod 3$), and sum diagonals ($(y + x) \bmod 3$). A queen inside the grid is counted 4 times; every other queen is counted once. Hence:

$$
C + R + T + S = 24 + 3h.
$$

At least $e = 16 - C$ columns and $f = 16 - R$ rows of the grid are empty; their $ef$ intersections can be covered only by diagonals. For $e, f \ge 2$, the outermost empty rows and columns contain $2e + 2f - 4$ boundary intersections, and any diagonal meets that boundary at most twice, so $T + S \ge e + f - 2$ (the same bound holds if $e = 1$ or $f = 1$, since each diagonal then covers at most one intersection).

Whenever $C, R < 16$, substituting gives $24 + 3h = C + R + T + S \ge (16 - e) + (16 - f) + (e + f - 2) = 30$, so **$h \ge 2$: the grid contains at least two queens**. When $h = 2$, equality holds throughout: every available diagonal covers a pair of boundary intersections, those pairs partition the boundary, and all occupied lines in each of the four classes are distinct.

### 2. Enumerate the equality cases

Testing all weak compositions of 24 queens across the 9 grids leaves **3,012** distributions satisfying the perimeter inequality. For each 2-queen grid with $C, R < 16$, choose its empty rows and columns, pick the first unpaired boundary intersection, branch on its two diagonals (requiring each chosen diagonal to pair with another unpaired boundary intersection), and verify that the resulting diagonals cover all interior intersections as well. This examines 31 line-count shapes and leaves **21 surviving distributions**. [Distribution check](Main.lean) · [Boundary pairing](Local.lean)

### 3. Fit the grids together globally

Two grids sharing a residue class of rows, columns, or diagonals must agree on which lines are occupied. Trying every compatible global combination across the 21 distributions splits into two cases ([Global.lean](Global.lean)):

* **12 distributions with a strip of three 2-queen grids:** after transposing if needed, the strip fixes all occupied rows and both sets of occupied diagonals. A queen in row $y$ needs occupied diagonals $t = y - x$ and $s = y + x$ with $t + s = 2y$; every combination leaves some occupied row without such a pair.
* **9 distributions with four 2-queen grids in a cross:** these determine all 24 occupied columns and all 24 occupied rows. Any uncovered square on an empty row and empty column forces its remaining diagonal whenever the other is unavailable. After propagation, each surviving combination specifies 23 or 24 distinct labels of each diagonal slope; at most one entry per slope is missing (with multiplicity), forced by $\sum t = \sum y - \sum x$ and $\sum s = \sum y + \sum x$. Every combination fails one of those linear sums or the quadratic identity $\sum t^2 + \sum s^2 = 2\sum x^2 + 2\sum y^2$ (from $(y - x)^2 + (y + x)^2 = 2(x^2 + y^2)$).

Hence no 24-queen cover exists. Since any smaller cover could be enlarged to 24 queens, **$\gamma(Q_{48}) = 25$**.

## Run the verification

From this directory with the pinned Lean **4.35.0** toolchain (standard library only):

```sh
lake exe queens48
```

The executable regenerates all data from the board size, checks the 25-queen placement on all 2,304 squares, and exhausts the 3,012 histograms, 31 local shapes, and 21 global configurations.

## References

* [Östergård and Weakley (2001), *Values of Domination Numbers of the Queen's Graph*, pp. 10–11](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v8i1r29/pdf/)
* [Davies (21 November 2026), §9 (`hexagonmath.org/pdf/2611.00830v1`)](https://hexagonmath.org/pdf/2611.00830v1#page=19)
* [Dated prior-art audit](../PRIOR_ART.md)
