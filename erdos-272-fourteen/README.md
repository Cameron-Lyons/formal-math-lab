# Erdős #272 on fourteen points

**The maximum is 95.** We want distinct subsets of $\{1,\ldots,14\}$ such that every two intersect in a nonempty arithmetic progression. Singletons and pairs count as progressions. [Problem statement](https://www.erdosproblems.com/272)

**A family of 95.** Start with the $1+13+\binom{13}{2}=92$ sets of size at most three containing 7. For each $d=1,2,3$, take the five-term progression $P_d$ centered at 7 with step $d$. Delete the two nonprogression triples through 7 inside $P_d$. Add $P_d$ and its two four-term ends. The smallest gap in each changed set is $d$, so the three exchanges each gain one set.

Every intersection contains 7. Two of the original sets meet in at most two points. Two of the added progressions meet in a progression. A small set can meet an added set in a nonprogression only if it is one of the deleted triples. [Szabó’s construction, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf) · [Lean check of all 4,465 pairs](Erdos272Fourteen.lean)

**Why 96 is impossible.** Make a graph on the 16,383 nonempty subsets. Join two when their intersection is a nonempty progression. The empty set cannot meet another member, so a valid family of 96 is exactly a 96-clique.

The exhaustive check uses one rule. If we need $k$ more vertices, each group of pairwise nonadjacent candidates can supply at most one. Greedily remove $k-1$ such groups. If nothing remains, this branch is impossible. Otherwise try each uncovered vertex in turn. Keep its neighbors, including those in the groups, and exclude earlier choices. Every completion has a first uncovered vertex, so the recursion misses none.

Reflection $i\mapsto15-i$ halves the work. Fix a vertex order. For any clique and its reflection, the first vertex of their union belongs to one of the two. Searching that orientation leaves $(16{,}383+127)/2=8{,}255$ possible first vertices, since 127 nonempty subsets are their own reflection. The check rules out a 96-clique at every one. Any larger clique would contain 96 vertices, so the construction is optimal. [Exhaustive verifier](upper.cpp)

## Reproduce

Run in this directory. The C++20 program checks the upper bound. OpenMP runs the independent starting cases in parallel. Lean checks the construction.

```sh
c++ -std=c++20 -O3 -march=native -fopenmp -DREPORT_PROGRESS upper.cpp -o /tmp/erdos272-upper
OMP_NUM_THREADS=7 /tmp/erdos272-upper
lake --wfail build
lake env leanchecker --fresh Erdos272Fourteen
```

For arbitrary $N$ the conjectured maximum is $1+\binom{N}{2}+\lfloor(N-1)/4\rfloor$. A separate rank argument proves this value when at most $\lfloor(N-1)/4\rfloor$ members contain a seven-term progression. The unrestricted formula remains open. The rank bound also speeds up the search at $N=14$. [General theorem](rank.md) · [Rank-based verifier](../erdos-272-thirteen/clique_search/verify.cpp)
