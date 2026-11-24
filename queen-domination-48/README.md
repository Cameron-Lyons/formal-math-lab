# Why the 48 × 48 board needs 25 queens

A known placement of 25 queens covers all 2,304 squares. The checker verifies the coordinates directly. It remains to rule out 24. [Placement](Main.lean) · [Östergård and Weakley, pp. 10–11](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v8i1r29/pdf/)

**Count the boundary squares.** Color a square `(x,y)` by the pair `(x mod 3, y mod 3)`. Each of the nine colors forms a 16 × 16 grid. Fix one grid and let `h` be the number of queens in it. Let `C,R,T,S` count queens in the four residue classes through it, for columns, rows, differences `y−x`, and sums `y+x`. A queen inside the grid counts four times. Each other queen counts once. Hence

```text
C + R + T + S = 24 + 3h.
```

At least `16−C` of the grid's columns and `16−R` of its rows are empty. If there are `e` empty columns and `f` empty rows, their intersections can be covered only by diagonals. For `e,f ≥ 2`, the outermost empty rows and columns contain `2e+2f−4` such intersections. A diagonal meets their boundary at most twice. Thus `T+S ≥ e+f−2`. The same bound holds when one of the two sets is a singleton, since each diagonal then covers at most one intersection.

Whenever `C,R < 16`, this gives `24+3h ≥ 30`, so **the grid contains at least two queens**. If it contains exactly two, equality holds throughout. Every available diagonal must cover a pair of boundary intersections, and those pairs partition the boundary. The occupied lines in each of the four classes are all distinct.

**Enumerate the equality cases.** Try each distribution of 24 queens among nine grids. The inequality leaves 3,012 distributions. For each two-queen grid with `C,R<16`, choose its empty rows and columns. Take the first unpaired boundary intersection and try its two diagonals in turn. A choice must pair it with another unpaired intersection. After pairing the boundary, check that the chosen diagonals cover every interior intersection too. This examines 31 different combinations of line counts and leaves **21 distributions**. [Distribution check](Main.lean) · [Boundary pairing](Local.lean)

**Fit the grids together.** Two grids that describe the same rows, columns or diagonals must agree on which lines are occupied. The checker tries every compatible combination. Only two arrangements occur among the 21 distributions. [Global check](Global.lean)

- **Twelve distributions have a strip of three two-queen grids.** After transposing if needed, the strip determines all occupied rows and both sets of occupied diagonals. A queen in row `y` needs a difference `t` and a sum `s` with `t+s=2y`. Every combination leaves some occupied row without such a pair.
- **Nine distributions have four two-queen grids arranged in a cross.** They determine all 24 occupied columns and all 24 occupied rows. A square on two empty axes forces its only possible diagonal whenever its other diagonal is unavailable. After enforcing these requirements, each surviving combination specifies 23 or 24 distinct labels of each slope. With 24 queens there is at most one missing entry of each slope, counting repetitions. Its value is forced by `Σt=Σy−Σx` or `Σs=Σy+Σx`. Every combination fails one of those sums or the identity `Σt²+Σs²=2Σx²+2Σy²`, obtained by adding `(y−x)²+(y+x)²=2(x²+y²)` over the queens.

Thus 24 queens cannot cover the board. A smaller cover could be enlarged to 24, so the minimum is exactly **25**.

## Run the proof

From this directory, run the following with the pinned Lean toolchain.

```sh
lake exe queens48
```

The program regenerates its data from the board size and checks the 25-queen placement. It uses Lean's standard library and runs as a compiled exhaustive enumeration. The counting argument above explains why its checks cover every possible placement.
