# Longest Snakes on a $15 \times n$ Grid

On a grid with 15 rows and $n$ columns, a **snake** (an **induced path** in the grid graph) is a chain of distinct cells in which consecutive cells share a horizontal or vertical edge and **no two non-consecutive cells touch orthogonally** (diagonal touches at a corner are permitted, but edge-to-edge self-contact is forbidden).

Let $L(n)$ be the maximum number of cells in a snake on a $15 \times n$ grid of positive width $n$. Then

$$
\boxed{L(n) = \left\lfloor \frac{28n + 10}{3} \right\rfloor}
$$

for **every positive width $n$ except eleven explicit small-width exceptions**:

| $n$ | 1 | 2 | 3 | 4 | 5 | 8 | 11 | 13 | 15 | 19 | 25 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $L(n)$ | 15 | 23 | 32 | 41 | 49 | 77 | 105 | 123 | 142 | 179 | 235 |

In particular, adding 3 columns adds **28 cells** — $L(n + 3) = L(n) + 28$ — for every $n \ge 26$ (asymptotic density $\frac{28}{15 \times 3} = \frac{28}{45} \approx 62.2\%$). The onset $n \ge 26$ is **sharp**, because $L(28) - L(25) = 264 - 235 = 29$.

| | |
| --- | --- |
| **Result** | Exact closed-form formula $L(n) = \lfloor (28n + 10)/3 \rfloor$ for every $15 \times n$ grid ($n \ge 1$), with 11 small-width exceptions |
| **Periodicity** | $L(n + 3) = L(n) + 28$ for $n \ge 26$ (sharp onset); repeating tile and transfer-matrix period are **6 columns / +56 cells** |
| **Exact boundary verifier** | C++17 transfer-matrix checker: [frontier.cpp](frontier.cpp) (4,473,453 states) |
| **Explicit construction** | [construct_snake.py](construct_snake.py) (direct grid-adjacency verification) |
| **Trust boundary** | Compiled C++17 exact integer arithmetic outside any proof-assistant kernel |

---

## Proof via frontier dynamic programming

### The big idea

Even though the final length formula gains 28 cells every **3** columns, the actual snake weaving across the 15-row strip returns to the *exact* same vertical cross-section every **6** columns, gaining $2 \times 28 = \mathbf{56}$ cells per 6-column cycle.

Because the strip has fixed height 15, there are only finitely many ways a partial snake can intersect a vertical cut between columns. Showing that every reachable boundary state gains **exactly 56 cells** between width 40 and width 46 locks in the 6-column shift $L(n + 6) = L(n) + 56$ for all larger widths at once.

### Boundary invariance

Cut a snake vertically between two columns. The prefix to the left of the cut may consist of several disconnected path segments (which later columns will connect). On its rightmost column, record:

- which cells are occupied,
- which occupied cells already have two occupied neighbors (degree 2), and
- which occupied cells belong to the same path component (or record **"finished"** if the entire snake ended before the cut).

Call this summary the prefix's **boundary**.

**Key lemma.** *Two prefixes with the same boundary admit the exact same set of legal endings.*

*Why:* Attach the exact same pattern of cells to the right of both prefixes. The occupied cells at the cut fix every horizontal edge crossing it; the degree information decides whether any crossing edge creates an illegal degree-3 branch; and the component memberships determine which path pieces merge and whether they form an illegal cycle. Any prefix component that does not touch the cut can never connect to future cells, so it is valid only when it is the entire finished snake.

### The exact 6-column shift at widths 40 and 46

Let $D_w(s)$ be the greatest number of cells in a valid prefix of width $w$ having boundary $s$. Because any snake can be shifted left until it hits column 1, we may require every prefix to meet column 1.

The finite computation ([Finite verifier](frontier.cpp)) verifies two things directly:

1. **Small widths:** $L(w)$ matches the stated formula (and eleven exceptions) through width **46**.
2. **Uniform boundary shift:** Widths **40** and **46** have the exact same set of reachable boundaries, and for every reachable boundary $s$,

$$
D_{46}(s) = D_{40}(s) + 56.
$$

Now fix any legal ending in the next $k \ge 0$ columns. For every boundary $s$ compatible with that ending, the best prefix at width 46 has **56 more cells** than at width 40, and the ending contributes the exact same number of cells to both. Taking the maximum over all compatible boundaries and endings yields

$$
L(46 + k) = L(40 + k) + 56 \qquad \text{for every } k \ge 0.
$$

The proposed floor formula $\lfloor (28n + 10)/3 \rfloor$ also increases by $\frac{28 \cdot 6}{3} = 56$ every six columns. The six directly checked widths $40, 41, 42, 43, 44, 45$ seed the recurrence in every residue class modulo 6, proving the formula at every width $n \ge 46$ — while the direct check covers all widths $n \le 46$. $\square$

---

## How the finite computation works (and independent cross-check)

Start from an empty grid and process cells one at a time, scanning each column from top to bottom:

1. For each new cell, branch on both choices: **vacant** or **occupied**.
2. If occupied, add edges to all already-processed orthogonal neighbors, discarding any choice that creates a degree-3 branch or closes a cycle.
3. If a path component drops off the boundary, keep the state only if it is the sole component (transitioning to "finished," after which only vacant cells are allowed).
4. For each resulting boundary state, retain only the maximum cell count. At the right edge of width $w$, any "finished" state or single connected component gives a valid candidate for $L(w)$.

**Mid-column subtlety:** Partway through scanning a column, the cell most recently scanned still has two unprocessed neighbors (below and to the right), so the mid-column state also tracks whether that cell currently has degree 0. Once a full column finishes, the simpler between-column boundary from the proof suffices.

- **Verifier ([Frontier verifier](frontier.cpp)):** The between-column transition graph has **4,473,453** states, of which **4,470,124** are reachable at both widths 40 and 46.

---

## Constructing a longest snake

A single **6-column repeating block** works for every sufficiently large width across all six residue classes. Its six column bitmasks (from left to right, where bit 0 selects the top row) are:

```text
3511  7021  14041  28081  23407  30424
```

Counting set bits per column gives $9 + 9 + 9 + 9 + 11 + 9 = \mathbf{56}$ cells per block.

To build an optimal snake at any width $n \ge 1$, [Python constructor](construct_snake.py) uses:

- **Six `(left end, right end)` base pairs**, chosen by $n \bmod 6$. In residue order $0, 1, 2, 3, 4, 5$, the two ends alone have combined widths **18, 31, 20, 27, 16, and 29**. Inserting as many copies of the 6-column block as needed between them covers every width from that residue's base onward.
- **Twenty individual snakes** covering the widths below each residue's base.

**Worked check ($n = 100$):** Since $100 \equiv 4 \pmod 6$, the constructor takes the width-16 base (which has $L(16) = 152$ cells) and inserts $(100 - 16)/6 = 14$ copies of the 6-column block, producing $152 + 14 \cdot 56 = \mathbf{936}$ cells — matching $\lfloor (28 \cdot 100 + 10)/3 \rfloor = 936$.

The Python script verifies geometry directly from the raw occupied squares: for each residue's base pair it checks that the base is a valid snake of optimal length, that every component of the left end meets the cut, and that inserting one block restores the exact same boundary cells, degrees, and component partition (with all components still meeting the cut). By induction, any number of blocks can be inserted before the right end, adding 56 cells each time.

---

## Reproduce

Run from this directory on a POSIX system with GCC or Clang and Python 3.10 or later.

**Resource notes:** On the test machine, `frontier.cpp` used about **2 GiB of RAM**.

```sh
build_dir=$(mktemp -d)
c++ -std=c++17 -O3 frontier.cpp -o "$build_dir/frontier"
"$build_dir/frontier"
python3 construct_snake.py
```

To print the column bitmasks of an optimal snake for a particular width (for example, $n = 100$), run:

```sh
python3 construct_snake.py 100
```

## References

- First 15 widths agree with [OEIS A360917](https://oeis.org/A360917)
- [Tong Niu’s paper](https://arxiv.org/html/2611.26640v1) (all-width formulas through height 12)
- Preceding workspace computations: [Height 13](../height-13/README.md) · [Height 14](../height-14/README.md)
