# Longest snakes on a 15 × n grid

Let $L(n)$ be the maximum number of cells in an induced path on a 15-row grid of positive width $n$. Then

$$
\boxed{L(n)=\left\lfloor\frac{28n+10}{3}\right\rfloor}
$$

for every positive width except the eleven below.

| $n$ | 1 | 2 | 3 | 4 | 5 | 8 | 11 | 13 | 15 | 19 | 25 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $L(n)$ | 15 | 23 | 32 | 41 | 49 | 77 | 105 | 123 | 142 | 179 | 235 |

In particular, $L(n+3)=L(n)+28$ for every $n\ge26$. The onset is sharp since $L(28)-L(25)=264-235=29$.

## Proof

Cut a snake between two columns. The part to the left can consist of several paths. On its last column record which cells are occupied, which already have two neighbors, and which belong to the same path. If the snake has ended before the cut, record “finished.” Call this its boundary.

**Two prefixes with the same boundary admit exactly the same endings.** To see this, put the same cells to the right of both. The occupied cells at the cut determine every edge across it. The degree information determines whether an edge creates a branch. The path memberships determine which pieces join and whether they form a cycle. A prefix component that misses the cut can only be the entire finished snake.

Let $D_w(s)$ be the greatest size of a prefix of width $w$ with boundary $s$. We may require it to meet column one, since any snake can be translated left. The finite computation verifies the claimed lengths through width 46. It finds the same reachable boundaries at widths 40 and 46, with

$$
D_{46}(s)=D_{40}(s)+56
$$

for every such boundary. [Finite verifier](frontier.cpp)

Fix any ending in the next $k\ge0$ columns. For each boundary it fits, the best prefix at width 46 has exactly 56 more cells than at width 40, and the ending adds the same cells to both. Taking the maximum over all compatible boundaries and endings gives

$$
L(46+k)=L(40+k)+56.
$$

The proposed floor formula also gains 56 every six columns. The six checked widths 40 through 45 start the recurrence in every residue class. This proves the formula at all larger widths, and the finite check covers the smaller ones. $\square$

## How to check the finite calculation

Start with an empty grid. For each new cell try both choices, vacant and occupied. If occupied, draw all edges to its already processed neighbors. Discard any choice that creates a branch or cycle. If a component leaves the boundary, keep it only if it is the sole component, and allow only empty cells thereafter. For each resulting boundary keep the greatest cell count. A finished snake or a single connected path at the right edge gives a candidate for $L(w)$.

The verifier scans a column from top to bottom. Mid-column, the last cell scanned still has two possible new neighbors, so it also records whether that cell has degree zero. At a cut between whole columns the boundary in the proof suffices. There are 4,473,453 such states in the transition graph, and 4,470,124 are reachable at both widths 40 and 46. An independent verifier instead pairs the edges that cross the cut and obtains the same 56-cell identity. [Frontier verifier](frontier.cpp) · [Crossing-edge verifier](crossings.cpp)

## Constructing a longest snake

The same six-column block works for every sufficiently large width. Its column masks, from left to right, are

```text
3511  7021  14041  28081  23407  30424
```

Bit zero selects the top row. Choose a left and a right end by the width modulo six. In residue order $0,1,2,3,4,5$, the two ends alone have widths $18,31,20,27,16,29$. Insert as many copies of the block as needed between the ends. The constructor supplies individual snakes at the twenty widths below their residue's base. [Python constructor](construct_snake.py)

The geometric check builds every adjacency from the selected cells. For each pair of ends it checks that the base is a snake of optimal length. It also checks that each component in the left end meets the cut, and that inserting one block restores the same boundary cells, degrees, and component partition, with all components still meeting the cut. Thus any number of copies can precede the right end, each adding 56 cells. For example, at width 100 the constructor uses the width-16 base and 14 blocks, giving $152+14\cdot56=936$ cells.

## An upper bound using only degrees

Every snake has degree at most two at each cell and satisfies

$$
\sum_{v\text{ occupied}}(2-\deg v)=2.
$$

Indeed, a path on $m$ cells has $m-1$ edges. Conversely, a board satisfying these two conditions consists of one path and any number of disjoint cycles. Allowing the cycles gives an upper bound.

For this bound a cut needs only the accumulated degree deficit and the occupancy requirements from the cells across the cut. Each old neighbor either requires the next cell to be occupied, requires it to be vacant, or leaves the choice free. Let $U_w(s)$ be the most cells one can add in $w$ columns starting from cut state $s$ and ending with total deficit two. A backward calculation checks the maxima through width 34 and verifies

$$
U_{34}(s)\le U_{28}(s)+56
$$

on all 2,764,097 cut states. Prepending the same $k$ columns preserves this upper bound. Since the floor formula also gains 56 every six columns, the checked widths 28 through 33 give the upper bound at every larger width.

The degree bound is one cell too high at four small widths. At widths $11,15,19,25$ it gives $106,143,180,236$, respectively. Starting from the empty board, the verifier follows every move that can still attain that width's maximum. As soon as a move closes a cycle, that entire branch is ruled out. All optimal branches at these four widths are ruled out this way, so each snake has at most $105,142,179,235$ cells at the respective width. The explicit snakes above attain the resulting bounds at every width. [Degree and cycle checks](degree_bound.cpp) · [Matching constructions](construct_snake.py)

## Reproduce

Run from this directory on a POSIX system with GCC or Clang and Python 3.10 or later. The two exact boundary verifiers each used about 2 GiB of RAM on the test machine. The degree verifier used about 3 GiB. The crossing-edge program also uses temporary disk space in its working directory and removes its scratch files automatically.

```sh
build_dir=$(mktemp -d)
c++ -std=c++17 -O3 frontier.cpp -o "$build_dir/frontier"
"$build_dir/frontier"
c++ -std=c++17 -O3 crossings.cpp -o "$build_dir/crossings"
"$build_dir/crossings"
c++ -std=c++17 -O3 degree_bound.cpp -o "$build_dir/degree_bound"
"$build_dir/degree_bound"
python3 construct_snake.py
```

To print the column masks for a particular width, run, for example, `python3 construct_snake.py 100`.

The first 15 widths agree with the rectangular-grid table. Niu gives all-width formulas through height 12, and the preceding workspace computations cover heights 13 and 14. [OEIS A360917](https://oeis.org/A360917) · [Niu’s paper](https://arxiv.org/html/2611.26640v1) · [Height 13](../height-13-snakes/README.md) · [Height 14](../height-14-snakes/README.md)
