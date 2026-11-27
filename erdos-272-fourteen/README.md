# Arithmetic-progression intersections on fourteen points

Let $t(N)$ be the largest size of a family of distinct subsets of
`{1, …, N}` in which every two distinct members intersect in a nonempty
arithmetic progression. Singletons and pairs are progressions. **The maximum
is $t(14)=95$.** Szabó’s construction supplies 95 members. A rank bound and
an exhaustive search rule out 96. [Erdős Problem #272](https://www.erdosproblems.com/272)

## A family of 95

Begin with all sets of size at most three containing 7. There are
`1 + 13 + 78 = 92`. For each step $d=1,2,3$, take the five-term progression
$x-2d,x-d,x,x+d,x+2d$ with centre $x=7$. Remove the triples
$\{x-2d,x,x+d\}$ and $\{x-d,x,x+2d\}$. Insert the full progression
and the two four-term progressions obtained by omitting one endpoint.
This gives $92-6+9=95$ sets. Any two of the original small sets intersect in
one or two points. The two discarded triples for each step are exactly the
nonprogression triples through $x$ inside its five-point progression.
The inserted progressions all contain $x$, and the nonempty intersection of
two arithmetic progressions is itself a progression. Lean checks
distinctness and all 4,465 intersections. [Lean witness](Erdos272Fourteen.lean) · [Szabó, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf)

## Why it suffices to test 12,394 starting pairs

1. **Families with a common point.** Yang’s Theorem 1.4 gives at most
   `1 + C(14,2) + floor(13/4) = 95` members. The C++ verifier checks this
   directly as well. For a fixed centre it uses the 92 sets of size at most
   three through the centre as separate classes. A larger nonprogression
   can be assigned to a triple it contains whose smallest enclosing
   progression it fails to contain. No two members assigned to that triple
   can have a progression as intersection. A matching places all but at most
   three of the larger progressions in distinct such classes, each containing
   a triple of the matched progression. This covers the star by at most 95
   classes, each permitting at most one member. [Yang’s theorem](https://arxiv.org/abs/2607.23004)
2. **Families with no common point.** For any $N$, at most
   $1+\binom N2$ members of such a family can avoid seven-term progressions.
   Their vectors recording the empty set and the pairs they contain are
   linearly independent. At $N=14$ the dimension is 92. Consequently a
   family of 96 must use at least four of the 752 subsets containing a
   seven-term progression. [Rank proof](rank.md) · [Counting inequality](score.md)
3. **Exhaustion.** Join two distinct subsets by an edge when their intersection
   is a nonempty progression. The desired family is a clique. Sort the 752
   distinguished subsets in consecutive reflection orbits under
   $i\mapsto15-i$. Reflect the whole family, if needed, so that its first
   distinguished set is the smaller member of its orbit. When that set is fixed
   by reflection the same choice applies to the second. There are 12,394
   compatible choices for these first two sets. For each pair the search asks
   for 94 further mutually adjacent common neighbours, including at least two
   later distinguished sets, with empty total intersection.

It is enough to exclude a clique of exactly 96. Any larger family contains
a 96-member subfamily, and the starred bound forces that subfamily to have
empty total intersection. A subfamily of this kind cannot contain a
singleton or the empty set, so the search starts with masks of size at least two.

At each search node, a clique needing $k$ more vertices must use a vertex
outside any $k-1$ independent sets. The verifier greedily constructs these
independent sets and branches on the uncovered candidates. It can also
branch on a smaller necessary set of candidates, such as those omitting a
point still common to the selected sets. On selecting a vertex it retains
only neighbours compatible with all earlier choices. The recursion is
exhaustive because it tries every vertex of the chosen necessary set, excluding
only choices already handled by an earlier branch. [Shared search code](../erdos-272-thirteen/clique_search/verify.cpp)

Across the 12,394 starting pairs the search visited **8,590,671 nodes**.
None admitted a completion, so every family on fourteen points has at most
95 members.

## What the argument gives for arbitrary $N$

The exact maximum is $1+\binom N2+\lfloor(N-1)/4\rfloor$ for the class of
families with at most $\lfloor(N-1)/4\rfloor$ members containing a seven-term
progression. The rank bound handles families with no common point. Yang handles
the common-point case, and Szabó attains the bound using only sets of size at
most five. The same formula for unrestricted families at arbitrary $N$ remains
open. [All-$N$ consequence](rank.md) · [Yang’s preprint](https://arxiv.org/abs/2607.23004)

## Reproduce

Run from this directory with Lean 4.36.0 and a C++23 compiler.

```sh
lake --wfail build
lake env leanchecker --fresh Erdos272Fourteen
c++ -std=c++23 -O3 -march=native -DERDOS272_N=14 ../erdos-272-thirteen/clique_search/verify.cpp -o /tmp/erdos272-check14
/tmp/erdos272-check14
```

The lower bound is checked by Lean's kernel. The upper bound uses the written
rank argument and the C++ exhaustion. The separate [score verifier](rank.cpp)
also checks the counting inequality on all 15,631 nonempty subsets avoiding
seven-term progressions. The preceding finite case is [$t(13)=82$](../erdos-272-thirteen/).
