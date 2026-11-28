# A second proof of the fifteen-point upper bound

Alongside the direct exhaustive clique search in [README.md](README.md), this note gives an **independent upper-bound proof** that no admissible family on $[15] = \{1, \ldots, 15\}$ can have $110$ members, using a linear-algebraic rank bound to cut down the search space before branching.

**Proof summary:**
- Mark every subset of $[15]$ that either contains a seven-term progression or is itself a five-term progression (**1,733** marked sets in total).
- A clean squared-norm identity proves that any admissible family can contain at most **106 unmarked sets**.
- Therefore, any 110-member family must contain at least **4 marked sets**.
- An exhaustive C++ search checks all **59,836** canonical choices for the first two marked members (up to reflection) and visits **367,041,673** search nodes; none extends to $110$. Because every larger family contains a 110-member subfamily, the maximum is at most **109**. [C++ verifier](../erdos-272-thirteen/clique_search/verify.cpp)

---

## Why there are at most 106 unmarked sets

**The big idea.** Unlike the general empty-total-intersection theorem in [erdos-272-fourteen/rank.md](../erdos-272-fourteen/rank.md), we avoid any five-term inclusion–exclusion analysis here simply by marking the 21 five-term progressions as well! With five-term progressions excluded from the unmarked pool, every progression of length $\le 6$ that can appear is *directly* indexed by a coordinate, so linear independence drops out in five lines.

Define two collections of small progressions in $[15]$:
- $U$: the empty set $\emptyset$ and all $\binom{15}{2} = 105$ pairs ($\lvert U \rvert = 106$).
- $V$: all singletons and all arithmetic progressions of lengths $3$, $4$, and $6$.

For any subset $S \subseteq [15]$, define the signed progression score
$$
q(S) = \#\{T \in U : T \subseteq S\} - \#\{T \in V : T \subseteq S\}.
$$
Across all $31{,}055$ nonempty subsets of $[15]$ that contain no seven-term progression, the verifier checks directly that $q(S) = 0$ if $S$ is an arithmetic progression and $q(S) > 0$ otherwise.

Now suppose for contradiction that an admissible family contains **more than $106$** unmarked members $A$.

1. **Find a nontrivial dependence on $U$.** Assign a real weight $c_A$ to each unmarked member $A$, and for any set $T$ write $w(T) = \sum_{A \supseteq T} c_A$. Because there are more unknowns $c_A$ than the $\lvert U \rvert = 106$ linear equations $w(T) = 0$ ($T \in U$), the homogeneous system has a **nonzero** solution.
2. **Apply the squared-norm identity.** Expanding $\sum_{T \in U} w(T)^2$ and comparing pairs $(A, B)$ shows
   $$
   0 = \sum_{T \in U} w(T)^2
     = \sum_{T \in V} w(T)^2 + \sum_A c_A^2 q(A).
   $$
   Why do all cross terms $c_A c_B$ ($A \ne B$) disappear? Each pair of distinct unmarked members $A, B$ intersects in a nonempty arithmetic progression of length at most $6$, so $q(A \cap B) = 0$!
3. **Force a contradiction at a largest surviving progression.** Every term on the right-hand side is nonnegative, so $w(T) = 0$ for all $T \in V$, and $c_A = 0$ whenever $q(A) > 0$ (i.e., whenever $A$ is not a progression). Take an inclusion-maximal set $P$ with $c_P \ne 0$. Then $P$ is an unmarked progression, so its length is $1, 2, 3, 4$, or $6$ (length $5$ and lengths $\ge 7$ were marked!), which puts $P \in U \cup V$. Because no larger surviving set contains $P$, we have $0 = w(P) = c_P$, contradicting $c_P \ne 0$. $\square$

Hence at most **106 unmarked sets** can belong to any admissible family on $[15]$.

---

## What the search checks

Build the compatibility graph on all nonempty subsets of $[15]$, joining two distinct sets by an edge whenever their intersection is a nonempty arithmetic progression.

1. **Starred-class exclusion (forcing every point to be omitted).** For each point $x \in [15]$, the verifier greedily partitions all sets containing $x$ into at most $109$ independent classes (no two sets in the same class are adjacent). Since a clique picks at most one set per class, any 110-clique must omit every point $x$ at least once.
2. **Canonical pairs of marked sets.** There are **1,733** marked sets (1,712 containing a seven-term progression plus the 21 five-term progressions). Group them into reflection orbits under $i \mapsto 16 - i$, ordering each orbit with the smaller bitmask first. Because a 110-clique needs at least 4 marked members, we may assume up to reflection that its earliest marked member is the smaller representative of its orbit—and if that member is reflection-symmetric, apply the same tie-breaker to its second marked member. This leaves **59,836** canonical starting pairs of compatible marked sets.
3. **Coloring branch-and-bound.** For each starting pair, the verifier searches their common neighbors for $108$ more mutually adjacent vertices containing at least two later marked sets. Whenever $k$ more vertices are needed, it greedily removes $k - 1$ independent classes and branches only on the remaining uncovered vertices (or, when a point $x$ is not yet omitted, branches directly on candidates omitting $x$).

The completed search visited **367,041,673** nodes and ruled out all 59,836 starting pairs. An independent enumeration also reproduced the common-neighbor counts for all 59,836 pairs.

---

## Reproduce

Run from this directory with a C++23 compiler:

```sh
c++ -O3 -std=c++23 -march=native -DERDOS272_N=15 ../erdos-272-thirteen/clique_search/verify.cpp -o /tmp/erdos272-rank15
/tmp/erdos272-rank15
```

The default command checks all 59,836 pairs. To split the work across runs, pass two zero-based indices defining a half-open range inside $[0, 59836)$.
