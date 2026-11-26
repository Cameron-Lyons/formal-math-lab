# Longest snakes on a 13 × n board

A snake is a chain of distinct squares. Consecutive squares share an edge, and no other two squares in the chain share an edge. Let $L(n)$ be the greatest number of squares in a snake on a 13-row board of width $n$.

For widths 1 through 6 the answers are **13, 20, 28, 36, 43, 51**. For every $n \ge 7$,

$$
L(n)=
\begin{cases}
8n+4 & n\bmod 6\in\{0,4,5\},\\
8n+3 & n\bmod 6\in\{1,2,3\}.
\end{cases}
$$

## Proof

**Two partial snakes with the same boundary allow exactly the same endings.** Scan the board from left to right. At the last column record which squares are occupied, which already have two neighbors, and which are joined through the part already scanned.

When a new square is filled, it joins every occupied neighbor. The degrees tell us whether this would give a square three neighbors. The connections tell us whether it would close a loop. If a component disappears behind the boundary, it can never join anything later; keep it only if it is the whole snake, in which case the remaining squares must stay empty. Every nonempty snake can be shifted left to meet the first column.

For each boundary keep the largest number of squares that can reach it. The finite check finds the same reachable boundaries at widths 53 and 59. For **every** reachable boundary, the best prefix at width 59 has exactly 48 more squares. The program compares all 514,021 entries, including the unreachable ones. [C++ verifier](frontier.cpp)

Now attach any $k$ more columns. For each boundary the same endings are available on both boards, so the best totals still differ by 48. Taking the maximum over boundaries gives $L(59+k)=L(53+k)+48$ for every $k\ge0$. The program also checks the formula directly at widths 1 through 59. Together these two finite checks prove the formula for every positive width.

The independent verifier uses an edge-crossing mate encoding with 620,950 boundary states and confirms the same exact period identity $V(59) = V(53) + 48$ in every coordinate (619,869 reachable) together with widths 1 through 59. [Independent verifier](alt_snake.cpp)

## Constructing an optimal snake

The constructor gives explicit snakes for widths 1 through 14. For larger widths it chooses fixed ends with a combined width from 15 through 20, then inserts as many copies of a six-column block as needed. Each copy adds 48 squares and restores the same boundary. The Python checker verifies the six base snakes and the repeatable boundary directly from grid adjacency. [Constructor](construct_snake.py) · [Interactive example for widths 4, 10, 16, 22, and 28](figures/repeating-snake.html)

## Reproduce

Run these commands in this directory with a C++23 compiler (also valid C++17) and Python 3.10 or later.

```sh
build_dir=$(mktemp -d)
c++ -std=c++23 -O3 frontier.cpp -o "$build_dir/frontier"
"$build_dir/frontier"
c++ -std=c++23 -O3 alt_snake.cpp -o "$build_dir/alt_snake"
"$build_dir/alt_snake"
python3 construct_snake.py
```

To obtain a particular snake, run `python3 construct_snake.py 100` with the desired width. It prints one integer per column. A set bit at position $r$, counting from zero, selects row $r+1$.

Both finite computations use compiled C++ and exact integer arithmetic outside the Lean kernel.

Niu proves the fixed-height problem through height 12 and identifies 13 as a next case in §8. The rectangular grid values are tabulated in OEIS A360917. [Niu, arXiv:2611.26640v1](https://arxiv.org/html/2611.26640v1#S8) · [OEIS A360917](https://oeis.org/A360917)
