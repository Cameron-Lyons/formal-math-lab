# Longest snakes on a 14 × n grid

Let $L(n)$ be the maximum number of squares in an induced path on a grid with 14 rows and $n$ columns. Write $n=6q+r$ with $0\le r<6$. Then, for every $n\ge18$,

$$
L(n)=52q+c_r,\qquad (c_0,c_1,c_2,c_3,c_4,c_5)=(3,12,20,30,38,47).
$$

The same formula holds at smaller positive widths with exactly eight exceptions.

| $n$ | 1 | 2 | 5 | 10 | 11 | 13 | 14 | 17 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $L(n)$ | 14 | 21 | 46 | 89 | 98 | 115 | 123 | 150 |

Outside those eight exceptions the formula is equivalently $L(n)=\lfloor(26n+11-(-1)^n)/3\rfloor$. In particular, $L(n+6)=L(n)+52$ for every $n\ge18$. The onset is sharp since $L(23)-L(17)=203-150=53$. The first 16 values agree with the rectangular grid table in the OEIS. Niu gives all-width formulas through height 12, and the lab's preceding computation handles height 13. [OEIS A360917 data](https://oeis.org/A360917/b360917.txt) · [Niu, §8](https://arxiv.org/html/2611.26640v1#S8) · [Height-13 proof](../height-13-snakes/README.md)

## Lean proof

The theorem `Height14.longest_snake` states that for every positive width some snake attains `formula n` and every snake has at most that length. A snake is a nonempty list of distinct grid squares. Two squares in the list share an edge exactly when they are consecutive. [Main theorem](lean/Height14.lean) · [Grid path definition](lean/Height14/Path.lean) · [Length formula](lean/Height14/Formula.lean)

The lower bound inserts an explicit 52-square path segment. For the upper bound, Lean proves that scanning a grid path follows the boundary transitions. Lean then checks the transition table and computes its scores backwards. At each boundary, the best continuation through 46 columns adds at most 52 more squares than the best continuation through 40. The same inequality propagates when another column is added. [Construction](lean/Height14/Witness.lean) · [Grid-to-boundary proof](lean/Height14/Grid.lean) · [Propagation](lean/Height14/Pumping.lean)

From this directory, run

```sh
cd lean
lake build
```

The package uses Lean 4.36.0 and its standard library. The finite checks use `native_decide`, so they trust Lean's compiler and native runtime. Lean computes the tables from source. The C++ programs and Python constructor below give separate checks. [Transition check](lean/Height14/RefinementCert.lean) · [Score check](lean/Height14/Certificate.lean)

## Why one finite check proves the formula

Scan the board a column at a time. A prefix of a snake may have several connected components because later columns can join them. Each component of the prefix is a path, possibly a single square. At the last column record which squares are occupied, which already have degree two, and which belong to the same component. These data decide every possible continuation. A new occupied square must join all its occupied neighbors. Connecting twice to the same component creates a cycle, and adding an edge to a degree-two square creates a branch. When a component leaves the boundary, it can never meet a later square. We keep such a prefix only if that component is the whole snake, and then permit only empty squares.

The first verifier builds this transition rule one square at a time. Partway through a column, one square at the bend of the boundary still has two unprocessed neighbors. For that square it also distinguishes degrees zero and one. Every transition adds exactly the edges forced by the occupied squares. Conversely, following the occupied squares of any snake passes all the tests. A nonempty prefix is accepted at the right edge precisely when it has a single component, including the case where the snake finished in an earlier column. We require the snake to meet column one, since any snake can be translated left until it does. [Frontier verifier](frontier.cpp)

Let $D_n(s)$ be the greatest number of occupied squares in a prefix of width $n$ with boundary state $s$, using $-\infty$ for an unreachable state. For $n\ge1$, appending a column applies a fixed operator $F$ to $D_n$. Each new entry is the maximum of an old entry plus the number of squares added by a legal transition. Thus $F(D+c)=F(D)+c$, with $-\infty+c=-\infty$.

The verifier exhaustively checks the formula at widths 1 through 47 and establishes

$$ D_{47}(s)=D_{41}(s)+52 \qquad\text{for every boundary state }s. $$

Of the 1,513,238 coordinates, exactly 1,511,341 are reachable at both widths. Applying $F$ another $k$ times gives $D_{47+k}=D_{41+k}+52$ for every $k\ge0$. Taking the maximum over accepting states proves the six-column recurrence for $n\ge41$. The checked widths cover the earlier cases and all six residues, giving the stated formula for every positive width.

The second verifier records promises about edges crossing the cut. It pairs the two exposed ends of each unfinished path, or marks an exposed end whose partner is already a final endpoint. Occupying the next square must honor each incoming promise, respect degree two, and keep the graph free of cycles. A completed component is accepted only when no other component is pending. This representation independently verifies the same vector identity at widths 41 and 47 on its own 1,776,869 states. Both finite checks use exact integer arithmetic in C++ and run outside the Lean kernel. [Crossing-edge verifier](alt_snake.cpp)

## Constructing a longest snake

A single six-column block works in all six residue classes. Its column masks from left to right are

```text
15799  9069  11995  10678  15212  1752
```

Bit zero selects the top row. The block contains 52 squares. The constructor supplies a left end and a right end for each residue, giving base widths 24, 19, 20, 15, 16, and 23 in residue order. It builds a snake from these two ends with any number of copies of the block between them, and supplies individual snakes for the remaining smaller widths.

The Python checker builds the induced graph directly from the squares. It verifies that the two ends alone form a snake of the claimed size and that appending one block to the left end restores the same boundary degrees and component partition. Every prefix component meets the boundary. It follows by induction that any number of copies fits, adding 52 squares each time. [Constructor and geometric checks](construct_snake.py)

## Reproduce

Run the following commands in this directory with a C++17 compiler and Python 3.10 or later.

```sh
build_dir=$(mktemp -d)
c++ -std=c++17 -O3 frontier.cpp -o "$build_dir/frontier"
"$build_dir/frontier"
c++ -std=c++17 -O3 alt_snake.cpp -o "$build_dir/alt_snake"
"$build_dir/alt_snake"
python3 construct_snake.py
```

To print the column masks of a longest snake at a particular width, run, for example, `python3 construct_snake.py 100`.
