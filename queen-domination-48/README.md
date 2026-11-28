# Queen domination number of the $48 \times 48$ chessboard: $\gamma(Q_{48}) = 25$

How few chess queens can you place on a $48 \times 48$ chessboard so that every one of its $48^2 = 2{,}304$ squares is either occupied by a queen or attacked along a row, column, or diagonal? This minimum count is the **queen domination number**, denoted $\gamma(Q_{48})$.

Östergård and Weakley (2001) exhibited a 25-queen dominating set ($\gamma(Q_{48}) \le 25$), and Davies (§9 of his 21 November 2026 preprint, `hexagonmath.org/pdf/2611.00830v1`) identified $n = 48$ as the next open even board. The compiled Lean 4 program in this folder (`lake exe queens48`) checks Östergård and Weakley's 25-queen placement across all 2,304 squares and exhaustively rules out any 24-queen dominating set via a **non-SAT** combinatorial proof, establishing $\gamma(Q_{48}) = 25$.

| Field | Summary |
| --- | --- |
| Problem | Queen domination number $\gamma(Q_{48})$ on the $48 \times 48$ board, Östergård and Weakley (2001), Davies (`hexagonmath.org/pdf/2611.00830v1`, §9) |
| Status | Solved ($\gamma(Q_{48}) = 25$). A compiled Lean search rules out 24 queens and verifies a 25-queen cover. |
| Entry point | `main` in [Main.lean](Main.lean) ([Local.lean](Local.lean), [Global.lean](Global.lean)) |
| Verification | `lake exe queens48` (Lean 4.36.0, stdlib only; compiled exhaustive enumeration rather than a kernel proof term, see argument below) |
| Prior art | Re-audited 26 November 2026: Aleksej Đukić published and certified $\gamma(Q_{48}) = 25$ on 22 November 2026 (OEIS A075458 rev. 125, `10.5281/zenodo.24537292`) using Davies' SAT frame method, two days before this folder. This program gives an independent non-SAT proof. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Proof that 24 queens cannot dominate the $48 \times 48$ board

[Main.lean](Main.lean) verifies directly that 25 explicit queen coordinates dominate all $48^2 = 2{,}304$ squares. Because any cover with fewer than 24 queens could be enlarged to 24 queens, proving $\gamma(Q_{48}) = 25$ reduces to ruling out a 24-queen dominating set.

### 1. Partition into nine $16 \times 16$ subgrids and squeeze the boundary

**The big idea.** Color every square $(x, y) \in \{0, \ldots, 47\}^2$ by its residues modulo 3: $(x \bmod 3, y \bmod 3)$. Because $48 = 3 \times 16$, this splits the chessboard into **nine** $16 \times 16$ subgrids.

Fix one of these nine subgrids and let $h$ be the number of queens placed *inside* it. Count the total number of queens across the entire $48 \times 48$ board whose lines pass through this subgrid:
- $C$: queens in the same column class ($x \bmod 3$),
- $R$: queens in the same row class ($y \bmod 3$),
- $T$: queens in the same difference-diagonal class ($(y - x) \bmod 3$),
- $S$: queens in the same sum-diagonal class ($(y + x) \bmod 3$).

A queen inside the chosen subgrid belongs to all four classes (counted 4 times). Meanwhile, every queen in any of the other 8 subgrids shares *exactly* one of the four residue classes with our subgrid (counted once). Summing across all 24 queens gives the exact double-counting identity:

$$
C + R + T + S = 4h + (24 - h) = 24 + 3h.
$$

Now look at the uncovered squares inside this $16 \times 16$ subgrid. At least $e = 16 - C$ columns and $f = 16 - R$ rows of the subgrid contain no queen, leaving an $e \times f$ grid of intersections that must be covered purely by diagonals:
- When $e, f \ge 2$, the outermost empty rows and columns trace a rectangular boundary (frame) of $2e + 2f - 4$ intersections. Because a straight diagonal hits that rectangular boundary at most twice, we need at least half as many diagonals: $T + S \ge e + f - 2$.
- When $e = 1$ or $f = 1$, all $ef$ intersections lie on a single line, so each diagonal covers at most one intersection, giving $T + S \ge ef = e + f - 1 > e + f - 2$; the bound $T + S \ge e + f - 2$ still holds.

Whenever $C < 16$ and $R < 16$ (so $e, f \ge 1$), plugging $C = 16 - e$, $R = 16 - f$, and $T + S \ge e + f - 2$ into our identity yields

$$
24 + 3h = C + R + T + S \ge (16 - e) + (16 - f) + (e + f - 2) = 30 \implies h \ge 2.
$$

Every such subgrid therefore holds **at least two queens**. Even better, whenever $h = 2$, equality holds with **zero slack**: every available diagonal must pair up two boundary intersections, those pairs must partition the entire boundary, and all occupied lines in each of the four classes ($C, R, T, S$) must be distinct!

### 2. Solve the zero-slack local puzzle on each 2-queen subgrid

Testing all weak compositions of 24 queens across the 9 subgrids leaves **3,012** distributions that satisfy the perimeter bound. For each 2-queen subgrid with $C, R < 16$, the program selects its empty rows and columns, grabs the first unpaired boundary intersection, branches on its two diagonals (requiring each to pair with another unpaired boundary intersection), and verifies that the chosen diagonals also cover every interior intersection of the $e \times f$ rectangle. Checking all **31** distinct line-count shapes eliminates almost everything, leaving just **21** surviving distributions ([Main.lean](Main.lean), [Local.lean](Local.lean)).

### 3. Patch the nine subgrids together globally

Whenever two subgrids share a residue class of rows, columns, or diagonals, they must agree on *which exact lines* are occupied. Exhausting all globally compatible combinations across the 21 surviving distributions splits cleanly into two cases ([Global.lean](Global.lean)):

- **12 distributions with a strip of three 2-queen subgrids:** Up to transposing the board, the strip fixes every occupied row and both sets of occupied diagonals. A queen in row $y$ at column $x$ occupies diagonals $t = y - x$ and $s = y + x$, which satisfy $t + s = 2y$. Every combination leaves some occupied row $y$ with no available diagonal pair summing to $2y$.
- **9 distributions with four 2-queen subgrids arranged in a cross:** Together these fix all 24 occupied columns and all 24 occupied rows. Whenever an uncovered square at the intersection of an empty row and empty column has one of its two diagonals unavailable, its other diagonal is forced. After propagating these forced diagonals, every surviving combination pins down 23 or 24 distinct labels of each diagonal slope—leaving at most one missing entry per slope (counting multiplicity). That missing entry is uniquely determined by the linear sum identities
  $$
  \sum t = \sum y - \sum x, \qquad \sum s = \sum y + \sum x.
  $$
  Every surviving combination then violates either those linear sums or the quadratic identity
  $$
  \sum t^2 + \sum s^2 = 2 \sum x^2 + 2 \sum y^2
  $$
  (which follows immediately from $(y - x)^2 + (y + x)^2 = 2(x^2 + y^2)$).

Hence no 24-queen dominating set exists, and $\gamma(Q_{48}) = 25$.

## Verification and trust boundary

Note that this folder verifies $\gamma(Q_{48}) = 25$ via a **compiled Lean 4 executable** performing the exhaustive case enumeration above rather than a kernel-checked proof term. (For a separate proof whose reduction and CNF encoding are kernel-checked and whose SAT refutations are verified by a proof-carrying LRAT checker, see [queen-domination-48-sat](../queen-domination-48-sat/).)

Run from this directory with the pinned Lean 4.36.0 toolchain (stdlib only):

```sh
lake exe queens48
```

The executable regenerates all data from scratch from the board size $n = 48$, checks the 25-queen placement on all 2,304 squares, and exhausts all 3,012 histograms, 31 local shapes, and 21 global configurations.

## References

- [Östergård and Weakley (2001), *Values of Domination Numbers of the Queen's Graph*, pp. 10-11](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v8i1r29/pdf/)
- [Davies (21 November 2026), §9 (`hexagonmath.org/pdf/2611.00830v1`)](https://hexagonmath.org/pdf/2611.00830v1#page=19)
- [Đukić (22 November 2026), OEIS A075458 certificate (`a075458_1.txt`)](https://oeis.org/A075458/a075458_1.txt) and [Zenodo preprint (`10.5281/zenodo.24537292`)](https://zenodo.org/records/24537292)
- [Prior-art audit](../PRIOR_ART.md)
