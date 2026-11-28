# Longest Snakes on a $14 \times n$ Grid

On a grid with 14 rows and $n$ columns, a **snake** (an **induced path** in the grid graph) is a path of distinct squares in which consecutive squares share a horizontal or vertical edge and **no two non-consecutive squares touch orthogonally** (diagonal corner touches are fine, but touching along an edge is forbidden).

Let $L(n)$ be the maximum number of squares in a snake on a $14 \times n$ grid. Write $n = 6q + r$ with $0 \le r < 6$. Then for **every width $n \ge 18$**,

$$
L(n) = 52q + c_r, \qquad (c_0, c_1, c_2, c_3, c_4, c_5) = (3, 12, 20, 30, 38, 47).
$$

Remarkably, the exact same formula also holds for all smaller positive widths **except eight explicit exceptions**:

| $n$ | 1 | 2 | 5 | 10 | 11 | 13 | 14 | 17 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $L(n)$ | 14 | 21 | 46 | 89 | 98 | 115 | 123 | 150 |

Outside those eight exceptions, the formula simplifies to a single closed-form expression:

$$
L(n) = \left\lfloor \frac{26n + 11 - (-1)^n}{3} \right\rfloor.
$$

In particular, adding 6 columns adds **exactly 52 squares** — $L(n + 6) = L(n) + 52$ — for every $n \ge 18$ (approaching density $\frac{52}{14 \times 6} = \frac{13}{21} \approx 61.9\%$). The onset $n \ge 18$ is **sharp**, because $L(23) - L(17) = 203 - 150 = 53$.

| | |
| --- | --- |
| **Result** | Exact formula for $L(n)$ on every $14 \times n$ grid ($n \ge 1$), with 8 small-width exceptions |
| **Periodicity** | $L(n + 6) = L(n) + 52$ for every $n \ge 18$ (sharp onset) |
| **Lean 4 formalization** | Theorem `Height14.longest_snake` in [lean/Height14.lean](lean/Height14.lean) (Lean 4.36.0 + stdlib; finite checks use `native_decide`) |
| **Independent verifiers** | Two C++17 transfer-matrix checkers ([frontier.cpp](frontier.cpp), [alt_snake.cpp](alt_snake.cpp)) + Python geometric constructor ([construct_snake.py](construct_snake.py)) |
| **Prior context** | First 16 values match [OEIS A360917 data](https://oeis.org/A360917/b360917.txt); follows [Niu, §8](https://arxiv.org/html/2611.26640v1#S8) (heights $\le 12$) and [Height-13 proof](../height-13-snakes/README.md) |

---

## Lean 4 formal proof

The main theorem `Height14.longest_snake` ([Main theorem](lean/Height14.lean)) proves both directions for every positive width $n$:

1. **Lower bound:** there exists a valid snake of length `formula n` ([Length formula](lean/Height14/Formula.lean)), and
2. **Upper bound:** every valid snake has length at most `formula n`.

Formally, a snake is a nonempty list of distinct grid squares in which two squares share an edge if and only if they are consecutive in the list ([Grid path definition](lean/Height14/Path.lean)).

**How the Lean proof works:**

- **Lower bound ([Construction](lean/Height14/Witness.lean)):** Constructs explicit base snakes and splices in a repeatable 52-square, 6-column path segment as many times as needed.
- **Upper bound ([Grid-to-boundary proof](lean/Height14/Grid.lean), [Propagation](lean/Height14/Pumping.lean)):** Proves structurally that scanning any grid snake column by column follows the boundary state-transition table, then checks the transition table ([Transition check](lean/Height14/RefinementCert.lean)) and computes optimal continuation scores **backwards** ([Score check](lean/Height14/Certificate.lean)). For every boundary state, the best continuation through **46** columns adds at most **52** more squares than the best continuation through **40** columns; by induction, that upper bound propagates each time another column is prepended.

### Building the Lean proof

From this directory, run:

```sh
cd lean
lake build
```

**Environment and trust boundary:** The package uses **Lean 4.36.0** and its standard library. Lean computes all tables from source, and the finite table/score checks use `native_decide`, so they trust Lean's compiler and native runtime. The two C++ verifiers and Python constructor below provide completely independent checks outside Lean.

---

## Why one finite computation proves the formula

### The big idea: transfer-matrix dynamic programming

When you cut a $14 \times n$ grid vertically between two columns, only 14 squares lie on the cut, leaving only finitely many possible boundary configurations. Scanning column by column turns the longest-snake problem into repeatedly applying a single fixed **max-plus operator** $F$ to a vector of boundary scores.

Because $F$ is **shift-invariant** — adding a constant $c$ to every entry shifts the output by that same constant $c$ — finding two widths (here **41** and **47**) whose score vectors differ by $+52$ in every coordinate immediately proves the 6-column recurrence for *all* larger widths.

### Boundary states and transitions

Scan the board one column at a time. A left prefix of a snake may consist of several disconnected path components (possibly single squares) that later columns will join together. At the rightmost column scanned so far, record:

- which of the 14 squares are occupied,
- which occupied squares already have degree 2, and
- which occupied squares belong to the same connected component.

These three pieces of data completely determine every legal continuation to the right:

- Adding an occupied square automatically connects it to all of its occupied orthogonal neighbors.
- Touching a degree-2 square creates a forbidden branch; touching the same component twice creates a forbidden cycle.
- If a component leaves the boundary (has no occupied square in the new column), it can never meet any future square. We keep such a prefix **only** if that component is the entire snake, and thereafter allow only empty squares.

The primary frontier verifier ([Frontier verifier](frontier.cpp)) executes transitions **one square at a time** down each column. Partway through a column, the single square sitting at the "bend" of the staircase boundary still has two unprocessed neighbors, so for that square alone the state also distinguishes degree 0 from degree 1. Every transition adds exactly the edges forced by the occupied squares, and conversely, tracing the occupied squares of any snake passes every check. A nonempty prefix is accepted at the right edge precisely when it has a single component (including a snake that finished in an earlier column). Since any snake can be translated left to touch column 1, we require the snake to meet column 1.

### The exact vector shift at widths 41 and 47

Let $D_n(s)$ be the maximum number of occupied squares in a valid width-$n$ prefix with boundary state $s$ (setting $D_n(s) = -\infty$ if $s$ is unreachable). For $n \ge 1$, appending one column applies a fixed operator $F$ to $D_n$, where each new coordinate is the maximum of an old coordinate plus the number of squares added by a legal transition. Therefore:

$$
F(D + c) = F(D) + c \qquad (\text{with } -\infty + c = -\infty).
$$

[frontier.cpp](frontier.cpp) exhaustively checks the formula for widths **1 through 47** and establishes the exact coordinate-wise shift

$$
D_{47}(s) = D_{41}(s) + 52 \qquad \text{for every boundary state } s.
$$

Out of all **1,513,238** boundary coordinates, exactly **1,511,341** are reachable at both widths 41 and 47 (and the remaining states are unreachable at both). Applying $F$ another $k$ times yields $D_{47 + k} = D_{41 + k} + 52$ for every $k \ge 0$. Taking the maximum over accepting states proves $L(n + 6) = L(n) + 52$ for all $n \ge 41$, and the checked widths 1 through 47 cover every smaller width and seed all six residue classes — proving the formula for every positive width.

### Independent crossing-edge verification

A second C++ program ([Crossing-edge verifier](alt_snake.cpp)) encodes the cut completely differently, recording **promises about horizontal edges crossing the cut**: it pairs the two exposed ends of each unfinished path, or marks an exposed end whose partner is already a final endpoint. Occupying the next square must honor every incoming edge promise, respect degree 2, and avoid cycles, and a completed component is accepted only when no other component is pending.

On its own state space of **1,776,869** states, it independently verifies the exact same vector shift between widths 41 and 47. Both C++ finite checks use exact integer arithmetic and run outside the Lean kernel.

---

## Constructing a longest snake

A single **6-column repeating block** works across all six residue classes modulo 6. Its six column bitmasks (from left to right, where bit 0 selects the top row) are:

```text
15799  9069  11995  10678  15212  1752
```

Counting set bits per column gives $11 + 8 + 10 + 8 + 9 + 6 = \mathbf{52}$ squares per block.

To construct a longest snake for any width $n \ge 1$, [construct_snake.py](construct_snake.py) provides:

- Six fixed `(left end, right end)` pairs — one for each residue $n \bmod 6 \in \{0, 1, 2, 3, 4, 5\}$ — having combined base widths **24, 19, 20, 15, 16, and 23**, respectively. Inserting $m \ge 0$ copies of the 6-column block between the ends covers every width from the residue's base upward.
- Individual optimal snakes for all remaining smaller widths below each residue's base.

The Python script independently checks the induced grid graph directly from raw square coordinates: it verifies that each base pair forms a valid snake of optimal length, that every component of the left end meets the cut, and that appending one block to the left end restores the exact same boundary degrees and component partition (with all components still meeting the cut). By induction, any number of blocks fits cleanly, adding 52 squares each time ([Constructor and geometric checks](construct_snake.py)).

---

## Reproduce

Run the following commands from this directory with a C++17 compiler and Python 3.10 or later:

```sh
build_dir=$(mktemp -d)
c++ -std=c++17 -O3 frontier.cpp -o "$build_dir/frontier"
"$build_dir/frontier"
c++ -std=c++17 -O3 alt_snake.cpp -o "$build_dir/alt_snake"
"$build_dir/alt_snake"
python3 construct_snake.py
```

To print the column bitmasks of a longest snake at a particular width (for example, $n = 100$), run:

```sh
python3 construct_snake.py 100
```

## References

- [OEIS A360917 data](https://oeis.org/A360917/b360917.txt) (first 16 widths agree)
- [Tong Niu, §8 — fixed-height snakes through height 12](https://arxiv.org/html/2611.26640v1#S8)
- [Height-13 proof](../height-13-snakes/README.md)
