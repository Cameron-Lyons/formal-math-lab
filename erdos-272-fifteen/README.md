# Arithmetic-progression intersections on fifteen points

**Theorem.** The largest family of distinct subsets of $[15]=\{1,\ldots,15\}$
whose pairwise intersections are nonempty arithmetic progressions has **109**
members. Singletons and pairs count as progressions. [Erdős problem #272](https://www.erdosproblems.com/272)

**Construction.** Start with the $1+14+\binom{14}{2}=106$ sets of size at most
three containing 8. For each $d=1,2,3$, take the five-term progression
$P_d=\{8-2d,8-d,8,8+d,8+2d\}$. Remove the two triples through 8 in $P_d$
that are not progressions. Add $P_d$ and the two four-term progressions obtained
by dropping one endpoint. Every changed set has smallest gap $d$, so the three
exchanges give $106-6+9=109$.

Every intersection contains 8. Two distinct small sets meet in at most two
points, and every retained triple inside an added progression is a progression.
The common terms of two added progressions also form a progression.
Lean checks all 5,886 intersections. [Szabó, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf) · [Lean witness](Erdos272Fifteen.lean)

**Upper bound.** Make a graph on the 32,767 nonempty subsets. Join two sets when
their intersection is a nonempty arithmetic progression. A family of size 110
is exactly a clique of size 110 in this graph.

Suppose a clique still needs $k$ vertices. Greedily remove $k-1$ classes of
candidates, with no two vertices in a class adjacent. A clique takes at most one
from each class, so every completion uses an uncovered vertex. Try each such
vertex in turn, keeping only its neighbors and skipping vertices already tried.
For each point $x$, the verifier also partitions all sets containing $x$ into
$c_x\le109$ such classes. At least $110-c_x$ clique members must therefore omit
$x$. Whenever the clique still needs a member omitting $x$, the verifier can
branch on those candidates.

Reflection $i\mapsto16-i$ reduces the number of starting cases. In a fixed order, let
$A$ be the first set in the union of a clique and its reflection. Search the
orientation containing $A$. A reflection-invariant set is determined by seven
mirrored pairs and the middle point, giving $2^8-1=255$ nonempty fixed sets.
Thus $(32{,}767+255)/2=16{,}511$ first sets need checking.

The verifier checked all **16,511** starting sets in **156,880,055** recursive
calls. None extends to 110. Every larger family would contain a family of 110,
so the maximum is 109. [Exhaustive verifier](upper.cpp) ·
[Fourteen-point search](https://github.com/Cameron-Lyons/formal-math-lab/blob/3709189f2c4c414134811f58668a7bba6ad7cc92/erdos-272-fourteen/upper.cpp)

## Reproduce

Run from this directory with a C++20 compiler and Lean 4.36.0. With OpenMP,
the verifier checks independent starting cases in parallel. Lean checks the construction.

```sh
c++ -O3 -std=c++20 -march=native -fopenmp upper.cpp -o /tmp/erdos272-check15
/tmp/erdos272-check15
lake --wfail build
lake env leanchecker --fresh Erdos272Fifteen
```

The default run covers all starting sets. For a partial run, pass the endpoints
of a zero-based half-open range in $[0,16511)$. Omit `-fopenmp` to build a
serial verifier.
