# Longest snakes on a 15 × n grid

Let $L(n)$ be the maximum number of cells in an induced path on a 15-row grid of positive width $n$. Then

$$
\boxed{L(n)=\left\lfloor\frac{28n+10}{3}\right\rfloor}
$$

for every positive width except the eleven below.

| $n$ | 1 | 2 | 3 | 4 | 5 | 8 | 11 | 13 | 15 | 19 | 25 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $L(n)$ | 15 | 23 | 32 | 41 | 49 | 77 | 105 | 123 | 142 | 179 | 235 |

In particular, $L(n+3)=L(n)+28$ for every $n\ge26$. The onset is sharp since $L(28)-L(25)=264-235=29$. The first 15 widths agree with the rectangular-grid table. Niu gives all-width formulas through height 12, and the preceding workspace computations cover heights 13 and 14. [OEIS A360917](https://oeis.org/A360917) · [Niu's paper](https://arxiv.org/html/2611.26640v1) · [Height 13](../height-13-snakes/README.md) · [Height 14](../height-14-snakes/README.md)

## Boundary computation

Scan the cells one column at a time, from top to bottom. A partial snake can have several components. Each must be a path, allowing singletons. Every component must still touch the scan boundary unless the snake has finished. The last scanned cell in each row is on this boundary. At the left board edge, treat the missing cells as vacant.

For each boundary cell record whether it is occupied, whether its current degree is two, and which path component contains it. Number the components in order of first appearance to give every partition a unique encoding. Partway down a column the most recently scanned cell, or *pivot*, can still acquire two neighbors, below and to the right. One extra bit records whether its degree is zero. Every other boundary cell has at most one remaining neighbor, so degrees zero and one allow exactly the same future choices there. At a whole-column cut the extra bit is cleared.

There are two choices for each new cell.

- **Leave it vacant.** The cell on its left leaves the boundary. If each component still touches the boundary, continue scanning. If a component has just lost its last boundary cell, it can never join a later cell. Reject the choice if another component exists. If the lost component is the only one, enter a finished state that permits only vacant cells.
- **Occupy it.** Join it to every occupied neighbor on its left or above. These are all its previously scanned neighbors. Reject a neighbor of degree two, which would branch, and reject two neighbors belonging to the same component, which would close a cycle. Otherwise join the incident components, or start a singleton when both neighbors are vacant. Record the updated component names and degrees.

These rules add every edge of the induced graph exactly once. By induction, each retained prefix is a path forest or a single finished path. Conversely, scanning any snake passes every test. A component of its prefix that disappears behind the boundary must already be the entire snake. At the right edge, accept the finished state and every live state with exactly one component. Translate a snake left until it meets column one. This preserves its length and lets the computation discard the never-started state after the first column.

After scanning the first $r$ rows of a column, the boundary consists of vertical pieces of lengths $r$ and $15-r$. Each occupied run lies in one component, so there are at most

$$
\left\lceil \frac r2\right\rceil+
\left\lceil \frac{15-r}{2}\right\rceil=8
$$

components. Each row therefore needs one of 17 codes (vacant, eight unsaturated labels, eight saturated labels). Five base-17 digits fit in 21 bits. Three such groups and the pivot flag fit in one 64-bit word. The program compares full keys when interning states.

## Why one pair of widths suffices

Let $D_n(s)$ be the greatest number of occupied cells in a prefix meeting column one and having boundary state $s$ after column $n$. Give unreachable states score $-\infty$. Merging two prefixes with the same state preserves all future choices by the transition rules above. Thus, for $n\ge1$, appending a column applies the same operator $F$ to $D_n$. Each new coordinate is the maximum of predecessor scores plus the number of filled cells in the column. Consequently $F(D+c)=F(D)+c$, using $-\infty+c=-\infty$.

The finite computation checks the stated lengths at widths 1 through 46 and proves

$$
D_{46}(s)=D_{40}(s)+56\qquad\text{for every }s.
$$

There are 4,473,453 column-boundary states in the transition graph, about 2.96 times the height-14 count of 1,513,238. Exactly 4,470,124 coordinates are reachable at both widths. The verifier checks the equality on finite scores and checks that both scores are unreachable at each remaining coordinate. [Frontier verifier](frontier.cpp)

Applying $F$ another $k$ times gives $D_{46+k}=D_{40+k}+56$ for all $k\ge0$. Taking the maximum over accepting states gives $L(n+6)=L(n)+56$ for $n\ge40$. Each finite maximum is attained by a sequence of skip/fill choices. The formula $f(n)=\lfloor(28n+10)/3\rfloor$ satisfies $f(n+6)=f(n)+56$. Agreement on the six consecutive widths 40 through 45 therefore proves $L(n)=f(n)$ for all $n\ge40$. The same finite run covers every smaller width. In particular, the shorter three-column recurrence for the optimum follows from the formula.

## Independent check

A second verifier records which edges the prefix promises to extend across the cut. The two crossing ends of each unfinished path are paired. A single crossing end indicates that the path's other endpoint is already final. Reading the cut in geometric order, endpoints of two disjoint planar paths cannot interleave, so matching parentheses recover all pairs. A separate flag records an occupied neighbor that forbids occupation across the cut.

At each new cell, the verifier honors the incoming edge promises and chooses outgoing edges subject to the degree bound. It rejects cycles, more than two permanently fixed endpoints, and completion of one path while another is unfinished. Conversely, the actual edges of any snake specify choices that pass these tests. A snake ending at the right edge has made no promise past the board and reaches the finished state.

This verifier independently finds $D_{46}=D_{40}+56$ on its 5,087,024 boundary states, including 5,083,695 reachable at each width. Both programs use integer arithmetic. The finite parts of the proof are exhaustive C++ computations. [Crossing-edge verifier](crossings.cpp)

## Constructing a longest snake

The same six-column block works for every sufficiently large width. Its column masks, from left to right, are

```text
3511  7021  14041  28081  23407  30424
```

Bit zero selects the top row. Choose a left and a right end by the width modulo six. In residue order $0,1,2,3,4,5$, the two ends alone have widths $18,31,20,27,16,29$. Insert as many copies of the block as needed between the ends. The constructor supplies individual snakes at the twenty widths below their residue's base. [Python constructor](construct_snake.py)

The geometric check builds every adjacency from the selected cells. For each pair of ends it checks that the base is a snake of optimal length. It also checks that each component in the left end meets the cut, and that inserting one block restores the same boundary cells, degrees, and component partition, with all components still meeting the cut. Thus any number of copies can precede the right end, each adding 56 cells. For example, at width 100 the constructor uses the width-16 base and 14 blocks, giving $152+14\cdot56=936$ cells.

## Reproduce

Run from this directory on a POSIX system with GCC or Clang and Python 3.10 or later. The C++ verifiers each used about 2 GiB of RAM on the test machine. The crossing-edge program also uses temporary disk space in its working directory and removes its scratch files automatically.

```sh
build_dir=$(mktemp -d)
c++ -std=c++17 -O3 frontier.cpp -o "$build_dir/frontier"
"$build_dir/frontier"
c++ -std=c++17 -O3 crossings.cpp -o "$build_dir/crossings"
"$build_dir/crossings"
python3 construct_snake.py
```

To print the column masks for a particular width, run, for example, `python3 construct_snake.py 100`.
