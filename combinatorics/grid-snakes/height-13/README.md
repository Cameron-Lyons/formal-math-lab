# Longest Snakes on a $13 \times n$ Grid

On a rectangular grid of 13 rows and $n$ columns, a **snake** (in graph theory, an **induced path**) is a chain of distinct grid squares where consecutive squares share a horizontal or vertical edge, and **no two non-consecutive squares touch orthogonally** (touching diagonally at a corner is allowed, but sharing an edge is forbidden). For example, a C-shaped path leaves an empty "buffer" row between parallel segments so the snake never touches itself:

```text
# # #   <- valid 7-square snake (non-consecutive squares never share an edge)
. . #      filling the middle-left or center square would create an illegal touch
# # #
```

Let $L(n)$ be the maximum number of squares in a snake on a $13 \times n$ board.

For widths $n = 1$ through $6$, the exact maxima are **13, 20, 28, 36, 43, 51**. For **every width $n \ge 7$**,

$$
L(n) =
\begin{cases}
8n + 4 & n \bmod 6 \in \{0, 4, 5\}, \\
8n + 3 & n \bmod 6 \in \{1, 2, 3\}.
\end{cases}
$$

In particular, adding 6 columns adds **exactly 48 squares** ($L(n + 6) = L(n) + 48$) for every $n \ge 7$ — packing $\frac{48}{13 \times 6} = \frac{8}{13} \approx 61.5\%$ of the grid in the limit.

| | |
| --- | --- |
| **Result** | Exact closed-form formula for $L(n)$ on every $13 \times n$ grid ($n \ge 1$) |
| **Periodicity** | $L(n + 6) = L(n) + 48$ for every $n \ge 7$ |
| **Exhaustive verifier** | C++ frontier/transfer-matrix checker: [frontier.cpp](frontier.cpp) (514,021 states) |
| **Explicit construction** | [construct_snake.py](construct_snake.py) |
| **Trust boundary** | Compiled C++17/C++23 exact integer arithmetic outside the Lean kernel |

---

## Proof: Why one finite computation locks down every width

### The big idea

Why does adding 6 columns eventually add a fixed 48 squares, no matter how wide the board becomes? Because the board has a **fixed height of 13 rows**. If you slice a snake vertically between columns $n$ and $n + 1$, only 13 squares sit on the cut — so there are only finitely many ways the left half of a partial snake can look at that boundary.

Once we compute the best possible score for every boundary state column by column, if we ever reach two widths (here **53** and **59**) where *every* reachable boundary state has improved by the **exact same constant** (+48 squares), that constant shift propagates automatically to every wider board forever.

### Frontier dynamic programming

Scan the $13 \times n$ board from left to right, one column at a time. Because later columns can bridge separate pieces together, the left prefix of a snake may temporarily consist of several disconnected path segments.

At the rightmost column scanned so far, record the prefix's **boundary** (frontier state):

1. **Occupancy:** which of the 13 squares in the last column are occupied,
2. **Degree saturation:** which occupied boundary squares already have **two** occupied neighbors (and therefore cannot accept another neighbor without branching), and
3. **Connectivity:** which occupied boundary squares belong to the same connected component through the columns already scanned.

**Key invariance property:** *Two partial snakes with the same boundary allow the exact same set of legal endings.*

Indeed, whenever a new square is filled in the next column, it automatically gains an edge to every already-occupied orthogonal neighbor:

- The **degree** data tell us whether adding that square would push any square to degree 3 (illegal branch).
- The **connectivity** data tell us whether it would touch the same component twice (illegal loop/cycle).
- If a component disappears behind the boundary (having no occupied square in the new column), it can never connect to anything later; we keep such a prefix **only** if that component is the entire snake, in which case every remaining square to the right must stay empty.
- Because any nonempty snake can be shifted horizontally to touch column 1 without changing its length, we may restrict to snakes meeting the first column.

### The exact period identity at widths 53 and 59

For each boundary state $s$, track $V(n)[s]$: the maximum number of squares in any legal width-$n$ prefix ending in boundary $s$ (or unreachable). Appending one more column updates the vector of scores by a fixed max-plus rule, maximizing over legal transitions and adding the number of new occupied squares.

The primary C++ verifier ([frontier.cpp](frontier.cpp)) runs this dynamic program and discovers two finite facts:

1. **Direct base check:** The formula for $L(n)$ holds at every width $n = 1, 2, \dots, 59$.
2. **Uniform shift:** Widths **53** and **59** have the **exact same set of reachable boundary states**, and for **every** reachable boundary state, the best prefix at width 59 has **exactly 48 more squares** than at width 53. (The program compares all **514,021** boundary-state entries, including unreachable ones.)

Now attach *any* $k \ge 0$ additional columns to the right of both boards. For each boundary state $s$, the exact same legal endings are available on both the width-53 and width-59 boards, and any ending adds the exact same number of squares to both — so the best totals through boundary $s$ still differ by 48. Taking the maximum over all valid accepting boundaries yields

$$
L(59 + k) = L(53 + k) + 48 \qquad \text{for every } k \ge 0.
$$

Combined with the direct check for widths 1 through 59 (which already seeds all six residue classes modulo 6 at widths 53–58), this proves the formula for **every positive width $n$**.

## Constructing an optimal snake

To witness the lower bound constructively for every width $n \ge 1$, [construct_snake.py](construct_snake.py) provides:

- **Individual optimal snakes** for widths 1 through 14, and
- **A modular tiling for all widths $n \ge 15$:** six pairs of fixed left/right end caps (one pair per residue class modulo 6, with combined widths **15 through 20**), plus a single repeatable **6-column middle block**. Inserting as many copies of the 6-column block as needed between the ends adds **48 squares** per copy and restores the exact same boundary state.

The Python script directly verifies the six base snakes and the repeatable boundary directly from raw grid adjacency (no reliance on the C++ code).

---

## Reproduce

Run these commands from this directory with a C++23 compiler (also valid C++17) and Python 3.10 or later:

```sh
build_dir=$(mktemp -d)
c++ -std=c++23 -O3 frontier.cpp -o "$build_dir/frontier"
"$build_dir/frontier"
python3 construct_snake.py
```

To generate an explicit optimal snake at any width (for example, $n = 100$), run:

```sh
python3 construct_snake.py 100
```

It prints one integer bitmask per column: a set bit at position $r$ (counting from 0) selects row $r + 1$.

Both finite computations use compiled C++ and exact integer arithmetic outside the Lean kernel.

## References

- Tong Niu proves the fixed-height snake problem through height 12 and identifies height 13 as a next case in §8: [Niu, arXiv:2611.26640v1](https://arxiv.org/html/2611.26640v1#S8)
- Rectangular grid values are tabulated in [OEIS A360917](https://oeis.org/A360917)
