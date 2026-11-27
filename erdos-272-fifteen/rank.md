# A second proof of the fifteen-point upper bound

Mark the sets containing a seven-term progression and the
five-term progressions themselves. At most **106 unmarked sets** can occur in
one family, as shown below. A family of 110 therefore needs four marked members.
The finite search checks all **59,836** possibilities for its first two marked
members up to reflection. None extends to 110. Since every larger family contains
one of size 110, this proves the bound. [C++ verifier](../erdos-272-thirteen/clique_search/verify.cpp)

## Why there are at most 106 unmarked sets

Let $U$ consist of the empty set and all 105 pairs. Let $V$ consist of the
singletons and the progressions of lengths 3, 4, and 6. Define $q(S)$ by
counting the members of $U$ contained in $S$ and subtracting the number of
members of $V$ contained in $S$. On all 31,055 nonempty sets containing no
seven-term progression, the verifier checks that $q(S)=0$ for progressions and
$q(S)>0$ otherwise.

Suppose there are more than 106 unmarked members $A$. Give them real weights
$c_A$, and write $w(T)=\sum_{A\supseteq T}c_A$. The 106 homogeneous equations
$w(T)=0$ for $T\in U$ have a nonzero solution. Expanding squares gives

$$
0=\sum_{T\in U}w(T)^2=\sum_{T\in V}w(T)^2+\sum_A c_A^2 q(A).
$$

Indeed, each cross term cancels because $A\cap B$ is a progression of length
at most six and $q(A\cap B)=0$. Both sums on the right are nonnegative. Thus
$w(T)=0$ for $T\in V$, and only progressions can have nonzero weight. Take a
largest such progression $P$. Its length is 1, 2, 3, 4, or 6, so $P\in U\cup V$.
But then $0=w(P)=c_P$, a contradiction.

## What the search checks

Join two distinct nonempty subsets by an edge when their intersection is a
nonempty progression. For each point, the verifier greedily partitions the sets
containing it into at most 109 independent classes. A 110-clique must therefore
omit each point somewhere.

Order the marked sets in consecutive reflection orbits under $i\mapsto16-i$,
smaller bit mask first. Up to reflection the first marked member is the smaller
one in its orbit. If reflection fixes it, the same rule applies to the second.
For each such pair the verifier seeks 108 mutually adjacent common neighbors,
including at least two later marked sets. To seek $k$ vertices, it removes
$k-1$ independent sets. Every $k$-clique must use an uncovered vertex, so it
suffices to try each such vertex with its remaining neighbors. The search can
also branch on any choice still required, such as a set omitting a given point.

There are **1,733** marked sets, including the 21 five-term progressions. The
completed search visited **367,041,673** nodes. An independent enumeration
reproduced the common-neighbor counts for all 59,836 starting pairs.

## Reproduce

Run from this directory with a C++23 compiler.

```sh
c++ -O3 -std=c++23 -march=native -DERDOS272_N=15 ../erdos-272-thirteen/clique_search/verify.cpp -o /tmp/erdos272-rank15
/tmp/erdos272-rank15
```

The last command checks every pair. To split the search, pass two zero-based
indices for a half-open range and cover all of $[0,59836)$.
