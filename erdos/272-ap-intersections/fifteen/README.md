# Arithmetic-progression intersections on fifteen points

[Erdős Problem #272](https://www.erdosproblems.com/272) asks how many distinct subsets of $[n] = \{1, \ldots, n\}$ can be chosen so that every two different subsets intersect in a nonempty **arithmetic progression** (counting singletons and pairs as progressions).

**Theorem.** For $[15] = \{1, \ldots, 15\}$, the exact maximum family size is **109**.

* **Lower bound ($\ge 109$) — Lean 4:** [Erdos272Fifteen.lean](Erdos272Fifteen.lean) checks Szabó's 109-set construction across all $\binom{109}{2} = 5,886$ pairwise intersections.
* **Upper bound ($\le 109$) — Exhaustive C++20 clique search:** [upper.cpp](upper.cpp) exhaustively proves that no 110-set family exists across all **16,511** symmetry-reduced starting sets (**156,880,055** recursive calls).

## At a glance

| Field | Summary |
| --- | --- |
| Problem | [Erdős Problem #272](https://www.erdosproblems.com/272) at $n = 15$ |
| Theorem | Maximum family size on $[15] = \{1, \ldots, 15\}$ is **109** |
| Lower bound (Lean 4) | [Erdos272Fifteen.lean](Erdos272Fifteen.lean) (all 5,886 pairwise intersections checked) |
| Upper bound (C++20) | [Exhaustive verifier](upper.cpp) (16,511 starting sets, 156,880,055 recursive calls) |
| Related references | [Szabó, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf) · [Fourteen-point search](../fourteen/upper.cpp) |

## Why 109 is attainable (construction)

Following [Szabó, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf), build a family centered at the midpoint $8$:

1. Start with all subsets of $[15]$ of size at most 3 containing $8$: there are $1 + 14 + \binom{14}{2} = 106$ such sets.
2. For each step $d = 1, 2, 3$, take the five-term progression $P_d = \{8 - 2d, 8 - d, 8, 8 + d, 8 + 2d\}$:
   * **Remove** the 2 triples through $8$ inside $P_d$ that are *not* progressions.
   * **Add** $P_d$ itself and the 2 four-term progressions obtained by dropping either endpoint.

Every altered set has smallest gap $d$, so the three exchanges affect disjoint sets and yield $106 - 6 + 9 = 109$ sets.

**Why every pairwise intersection is a nonempty progression:** Every set contains $8$, so no intersection is empty. Two distinct original small sets meet in at most two points (automatically a progression); every retained triple inside an added progression is already a progression; and the common terms of any two added progressions also form a progression. Lean checks all **5,886** intersections in [Erdos272Fifteen.lean](Erdos272Fifteen.lean).

## Why 110 is impossible (exhaustive upper bound)

**Reformulation as a clique search.** Build a graph whose vertices are the $2^{15} - 1 = 32,767$ nonempty subsets of $[15]$, joining two sets by an edge whenever their intersection is a nonempty arithmetic progression. A valid family of size 110 is *exactly* a 110-clique (110 mutually adjacent vertices) in this graph.

Three pruning and symmetry-breaking techniques make an exhaustive search feasible:

1. **Coloring-based branch-and-bound:** Suppose the current partial clique still needs $k$ more vertices. Greedily pull out $k - 1$ independent classes of candidates (no two vertices in the same class are adjacent). Because a clique can pick at most one vertex from each class, every valid completion must use at least one **uncovered** vertex. The search branches on each uncovered vertex in turn, keeping only its neighbors and skipping vertices already tried.
2. **Starred-class branching (forcing missing points):** For every point $x \in [15]$, the verifier also partitions all sets containing $x$ into $c_x \le 109$ independent classes. A 110-clique can take at most $c_x$ sets containing $x$, so at least $110 - c_x$ clique members must *omit* $x$. Whenever the partial clique still needs a member omitting $x$, the verifier can immediately branch on the candidates omitting $x$.
3. **Reflection symmetry ($i \mapsto 16 - i$):** Reflecting $[15]$ around $8$ preserves arithmetic progressions and maps every clique to a clique of the same size. Fix an ordering of all 32,767 nonempty subsets, and for any clique let $A$ be the earliest set appearing in the union of the clique and its reflection; searching only the orientation containing $A$ keeps every counterexample. A reflection-invariant subset is determined independently on the 7 mirrored pairs and the middle point $8$, giving $2^8 - 1 = 255$ nonempty fixed sets. Pairing up the remaining non-symmetric sets leaves exactly

   $$
   \frac{32{,}767 + 255}{2} = 16{,}511
   $$

   starting sets to check.

The [exhaustive verifier](upper.cpp) (modeled on the [fourteen-point search](../fourteen/upper.cpp)) checked all **16,511** starting sets in **156,880,055** recursive calls and found that none extends to a 110-clique. Since any larger family would contain a 110-element subfamily, the maximum is **109**.

## Reproduce

Run from this directory with a C++20 compiler and Lean 4.36.0. With OpenMP, the verifier checks independent starting cases in parallel. Lean checks the construction.

```sh
c++ -O3 -std=c++20 -march=native -fopenmp upper.cpp -o /tmp/erdos272-check15
/tmp/erdos272-check15
lake --wfail build
lake env leanchecker --fresh Erdos272Fifteen
```

The default run covers all starting sets. For a partial run, pass the endpoints of a zero-based half-open range in $[0, 16511)$. Omit `-fopenmp` to build a serial verifier.
