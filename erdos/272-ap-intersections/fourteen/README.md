# Arithmetic-progression intersections on fourteen points

[Erdős Problem #272](https://www.erdosproblems.com/272) asks for the largest family of distinct subsets of $\{1, \ldots, n\}$ such that every two distinct members intersect in a nonempty **arithmetic progression** (counting singletons and pairs as progressions).

**Theorem.** On $\{1, \ldots, 14\}$, the exact maximum family size is **95**.

- **Lower bound ($\ge 95$) — Lean 4:** [Erdos272Fourteen.lean](Erdos272Fourteen.lean) certifies Szabó's 95-set construction by checking distinctness and all $\binom{95}{2} = 4{,}465$ pairwise intersections directly in Lean.
- **Upper bound ($\le 95$) — Exhaustive C++20 clique search:** [upper.cpp](upper.cpp) exhaustively proves that no 96-set family exists across all **8,255** symmetry-reduced starting sets.
- **General-$N$ restricted theorem:** A companion linear-algebraic rank proof establishes Szabó's conjectured formula $1 + \binom{N}{2} + \lfloor (N - 1)/4 \rfloor$ for *every* $N \ge 1$ whenever at most $\lfloor (N - 1)/4 \rfloor$ members contain a seven-term progression ([General theorem](rank.md)).

## At a glance

| Field | Summary |
| --- | --- |
| Problem | [Erdős Problem #272](https://www.erdosproblems.com/272) at $n = 14$ (plus general-$N$ rank theorem) |
| Theorem | Exact maximum on $\{1, \ldots, 14\}$ is **95** |
| Lower bound (Lean 4) | `Erdos272Fourteen.exists_family_95` in [Erdos272Fourteen.lean](Erdos272Fourteen.lean) (4,465 pairs checked) |
| Upper bound (C++20) | [Exhaustive clique verifier](upper.cpp) (8,255 reflection-reduced starting sets) |
| General-$N$ rank proof | [rank.md](rank.md), [score.md](score.md), [rank.cpp](rank.cpp), [Rank-based verifier](../thirteen/clique_search/verify.cpp) |
| Reference | [Szabó's construction, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf) |

---

## Why 95 is attainable (construction)

Following [Szabó's construction, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf), build a family centered around $7$:

1. Start with all subsets of $\{1, \ldots, 14\}$ of size at most $3$ that contain $7$: there are $1 + 13 + \binom{13}{2} = 92$ such sets.
2. For each step $d = 1, 2, 3$, take the five-term progression $P_d = \{7 - 2d, 7 - d, 7, 7 + d, 7 + 2d\}$ centered at $7$:
   - **Delete** the 2 triples through $7$ inside $P_d$ that are *not* progressions (namely $\{7 - 2d, 7, 7 + d\}$ and $\{7 - d, 7, 7 + 2d\}$).
   - **Add** $P_d$ itself and its 2 four-term subprogressions obtained by dropping either endpoint.

Every modified set has smallest consecutive gap $d$, so the three exchanges touch disjoint sets and each gives a net gain of $+1$, totaling $92 - 6 + 9 = 95$ sets.

**Why every pairwise intersection is valid:** Every member contains $7$, so no intersection is empty. Two original small sets intersect in at most two points (automatically a progression); two added progressions intersect in a progression; and a small set can meet an added progression in a nonprogression *only* if it is one of the deleted triples. Lean verifies all **4,465** pairs in [Erdos272Fourteen.lean](Erdos272Fourteen.lean).

---

## Why 96 is impossible (exhaustive upper bound)

**Graph reformulation.** Form a compatibility graph whose vertices are the $2^{14} - 1 = 16{,}383$ nonempty subsets of $\{1, \ldots, 14\}$, joining two sets by an edge whenever their intersection is a nonempty arithmetic progression. Because the empty set cannot intersect any other set nonemptily, a valid family of size $96$ is *exactly* a 96-clique in this graph.

Two simple ideas make an exhaustive clique search fast:

1. **Coloring-based branch-and-bound:** Suppose a partial clique still needs $k$ more vertices. Greedily peel off $k - 1$ independent groups of candidates (no two vertices in the same group are adjacent). Since a clique can take at most one vertex from each group, every valid completion must contain at least one **uncovered** vertex. If no candidates remain uncovered, prune the branch immediately; otherwise branch on each uncovered vertex in turn, restricting to its neighbors (including those inside the peeled groups) and excluding earlier choices. Every completion has a unique first uncovered vertex, so nothing is missed.
2. **Reflection symmetry ($i \mapsto 15 - i$):** Reflecting $\{1, \ldots, 14\}$ reverses arithmetic progressions and preserves clique size. Fix a total order on all $16{,}383$ nonempty subsets. For any clique $C$ and its reflection $\overline{C}$, the earliest vertex in $C \cup \overline{C}$ belongs to one of the two; searching only the orientation containing that earliest vertex cuts the work nearly in half. Exactly $2^7 - 1 = 127$ nonempty subsets are fixed by reflection (determined on the 7 mirrored pairs $\{1, 14\}, \ldots, \{7, 8\}$), leaving
   $$
   \frac{16{,}383 + 127}{2} = 8{,}255
   $$
   canonical starting vertices.

The [exhaustive verifier](upper.cpp) rules out a 96-clique at all **8,255** starting vertices. Because any larger family would contain a 96-member subfamily, the exact maximum is **95**.

---

## Reproduce

Run from this directory with a C++20 compiler and Lean 4.36.0. OpenMP parallelizes the independent starting cases; Lean checks the 95-set construction.

```sh
c++ -std=c++20 -O3 -march=native -fopenmp -DREPORT_PROGRESS upper.cpp -o /tmp/erdos272-upper
OMP_NUM_THREADS=7 /tmp/erdos272-upper
lake --wfail build
lake env leanchecker --fresh Erdos272Fourteen
```

For general $N$, Szabó's conjectured maximum is $1 + \binom{N}{2} + \lfloor (N - 1)/4 \rfloor$. A companion linear-algebraic rank argument proves this exact value for every $N$ whenever at most $\lfloor (N - 1)/4 \rfloor$ members contain a seven-term progression (and also speeds up the 14-point search), while the unrestricted formula remains open. [General theorem](rank.md) · [Rank-based verifier](../thirteen/clique_search/verify.cpp)
