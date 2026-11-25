# Classical Ramsey number R(3, 10)

The classical Ramsey number $R(3, 10)$ is the smallest $N$ such that every simple graph on $N$ vertices contains a triangle ($K_3$) or an independent set of size 10 ($\overline{K_{10}}$). Geoffrey Exoo's 39-vertex graph gives $R(3, 10) \ge 40$, and Vigleik Angeltveit (2025) proved $R(3, 10) \le 41$. Whether $R(3, 10)$ is 40 or 41 remains open.

The Lean 4 proofs here verify two non-isomorphic 39-vertex witnesses ($R(3, 10) \ge 40$: Exoo's 167-edge graph and a 172-edge graph), verify Kalbfleisch's unique 35-vertex $R(3, 9, 35)$ circulant ($R(3, 9) \ge 36$), prove structural constraints on any 40-vertex $R(3, 10, 40)$ graph (degree bound $\Delta \le 9$, dual-neighborhood reduction, weighted Mantel's theorem, and an Angeltveit-type edge/regularity dichotomy), prove that no one-vertex extension of Exoo's graph to 40 vertices avoids both $K_3$ and $\overline{K_{10}}$, rule out all 40-vertex circulant graphs and all 40-vertex graphs invariant under simultaneous rotation of two 20-vertex cycles, and prove the equivalence between $R(3, 10) \in \{40, 41\}$ and the unrestricted 40-vertex SAT formula.

In addition, three standalone C++23 programs in [scripts/](scripts/) run exhaustive checks outside the Lean kernel ruling out all Cayley graphs on the 14 groups of order 40, all 2-orbit bi-Cayley graphs on the 5 groups of order 20, and degree-4 vertices in $R(3, 10, 40)$ (assuming uniqueness of $R(3, 9, 35)$).

| Field | Summary |
| --- | --- |
| Problem | Classical Ramsey number $R(3, 10)$ ($40 \le R(3, 10) \le 41$), Exoo (1989) 39-vertex graph, Angeltveit (2025) upper bound 41 |
| Status | Lower bound 40 verified (two non-isomorphic 39-vertex witnesses), structural dichotomy and order-40 extension/symmetry obstructions proved; choice between 40 and 41 remains open. |
| Main theorems | `Ramsey310.ramsey_lower_bound`, `exoo_no_one_vertex_extension`, `Structural.r310_40_dichotomy`, `Structural.weighted_mantel`, `R39.r39_witness`, `Dense39.dense39_witness`, `Circulants.order40`, `TwoOrbits.two_cycles_of_length_twenty`, `SAT.value40_iff_unsat`, `SAT.value41_iff_sat` |
| Verification | `lake build` (Lean 4.36.0, stdlib only; all modules except `TwoOrbits` are kernel-checked; `TwoOrbits` LRAT check uses `native_decide`; `scripts/*.cpp` are unverified external C++23 exhaustive checks) |
| Prior art | Updated 25 November 2026: Kalbfleisch (1966) gave $C_{35}(\{1, 7, 11, 16\})$, Exoo (1989) proved $R(3, 10) \ge 40$, Angeltveit (2025) proved $R(3, 10) \le 41$ using weighted-Mantel / blow-up constraints, and Harborth and Krause (2003) and Coniglio et al. (2026) reported the circulant bound 38. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Why Exoo's 39-vertex graph cannot be extended by one vertex

Add a 40th vertex $v$ to Exoo's 39-vertex graph. If two neighbors of $v$ are adjacent, they form a triangle with $v$; otherwise the neighborhood of $v$ is an independent set. Lean checks ten explicit 9-vertex independent sets in Exoo's graph and proves that at least one of them contains no neighbor of $v$. Adjoining $v$ to that 9-set yields an independent set of size 10, ruling out every one-vertex extension ([Extension.lean](Extension.lean)).

## Weighted-Mantel dichotomy for $R(3, 10, 40)$

In any triangle-free 40-vertex graph $G$ with no independent 10-set, every vertex satisfies $\deg(v) \le 9$. Setting the degree deficit $w(v) = 9 - \deg(v) \ge 0$ and applying weighted Mantel's theorem ($2 \sum_u w(u) d_w(u) \le (\sum_u w(u))^2$) together with the triangle-free neighborhood edge-partition identity $2|E(G)| = 2|E(G - N[v])| + 2 \sum_{u \in N(v)} \deg(u)$ yields a sharp dichotomy ([Structural.lean](Structural.lean)):

* Either $G$ is 9-regular ($|E(G)| = 180$), and every dual neighborhood $G - N[v]$ on 30 vertices has exactly 99 edges; or
* Some vertex $v$ has degree $d \le 8$ and its dual neighborhood $G - N[v]$ on $39 - d$ vertices has at most $180 - 9d$ edges.

## Lean results

| Theorem (namespace `Ramsey310`) | File | What it proves |
| --- | --- | --- |
| `ramsey_lower_bound` | [Ramsey39.lean](Ramsey39.lean), [RamseyNumber.lean](RamseyNumber.lean) | Exoo's 39-vertex graph (167 edges) is triangle-free with no independent 10-set, proving $R(3, 10) \ge 40$. |
| `Dense39.dense39_witness`, `Dense39.dense39_twiceEdges`, `Dense39.not_ramseyProperty_39` | [CertVerify.lean](CertVerify.lean), [DenseWitness39.lean](DenseWitness39.lean) | Kernel-checks a second, independently constructed 39-vertex $R(3, 10, 39)$ witness with 172 edges (non-isomorphic to Exoo's 167-edge graph) via a 651-node edge/singleton clique-cover certificate tree. |
| `R39.r39_witness` | [CertVerify.lean](CertVerify.lean), [R39LowerBound.lean](R39LowerBound.lean) | Kernel-checks Kalbfleisch's unique 35-vertex $R(3, 9, 35)$ circulant $C_{35}(\{1, 7, 11, 16\})$ via a 159-node clique-cover certificate tree, proving $R(3, 9) \ge 36$. |
| `Structural.deg_lt_k`, `Structural.dual_nbhd_no_indep`, `Structural.weighted_mantel`, `Structural.twiceEdges_partition`, `Structural.r310_40_dichotomy` | [Structural.lean](Structural.lean) | Proves $\Delta < k$, dual-neighborhood reduction, weighted and unweighted Mantel's theorem, the triangle-free edge-partition identity, and the 9-regular vs. $|E(G - N[v])| \le 180 - 9d$ dichotomy for $R(3, 10, 40)$. |
| `exoo_no_one_vertex_extension` | [Extension.lean](Extension.lean) | Every choice of neighbors for a 40th vertex added to Exoo's graph creates a triangle or an independent 10-set. |
| `Circulants.order40` | [Circulants.lean](Circulants.lean) | Every 40-vertex circulant graph contains a triangle or an independent 10-set. |
| `TwoOrbits.two_cycles_of_length_twenty` | [TwoOrbits.lean](TwoOrbits.lean) | Every 40-vertex graph invariant under simultaneous rotation of two disjoint 20-cycles contains a triangle or an independent 10-set. |
| `SAT.value40_iff_unsat`, `SAT.value41_iff_sat` | [RamseySAT.lean](RamseySAT.lean) | For the unrestricted 40-vertex SAT formula (one variable per edge of $K_{40}$), unsatisfiability is equivalent to $R(3, 10) = 40$, and (assuming Angeltveit's $R(3, 10) \le 41$) satisfiability is equivalent to $R(3, 10) = 41$. |

## Compiled C++23 exhaustive checks (outside Lean)

These standalone programs are compiled and run outside the Lean kernel and carry the trust boundary of unverified C++ code:

| Script | Scope checked | Outcome |
| --- | --- | --- |
| [scripts/search_cayley40.cpp](scripts/search_cayley40.cpp) | All 14 non-isomorphic groups of order 40 (2,103,338 triangle-free Cayley graphs; 715,063 maximal within $\deg \le 9$), plus $C_{20}$ bicirculants | 0 $R(3, 10, 40)$ graphs |
| [scripts/search_sym40.cpp](scripts/search_sym40.cpp) | All 5 groups of order 20 ($C_{20}$, $\mathrm{Dic}_{20}$, $F_{20}$, $C_{10} \times C_2$, $D_{20}$) acting semiregularly with two orbits of size 20 (342,006 maximal triangle-free bi-Cayley graphs) | 0 $R(3, 10, 40)$ graphs |
| [scripts/check_r39_35_deg4.cpp](scripts/check_r39_35_deg4.cpp) | All 3,365 maximal independent sets of $C_{35}(\{1, 7, 11, 16\})$ (3,360 independent 8-sets; 191,100 pairwise-compatible MIS pairs) | 0 pairwise-compatible MIS triples (excludes degree-4 vertices in $R(3, 10, 40)$ assuming uniqueness of $R(3, 9, 35)$) |

## Verification

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

All Lean modules except [TwoOrbits.lean](TwoOrbits.lean) are kernel-checked with only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). The two-cycle theorem in [TwoOrbits.lean](TwoOrbits.lean) uses `native_decide` to validate its vertex sets and replay its LRAT certificate ([certificates/two-orbits.sets](certificates/two-orbits.sets), [certificates/two-orbits.lrat](certificates/two-orbits.lrat)), trusting the Lean compiler and runtime for those finite checks.

To reproduce the external C++23 exhaustive checks:

```sh
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror scripts/check_r39_35_deg4.cpp -o /tmp/check_deg4 && /tmp/check_deg4
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror scripts/search_cayley40.cpp -o /tmp/search_cayley40 && /tmp/search_cayley40
g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror scripts/search_sym40.cpp -o /tmp/search_sym40 && /tmp/search_sym40
```

## References

* [Kalbfleisch (1966)](https://doi.org/10.4153/CMB-1966-014-6) and Grinstead and Roberts (1982), $R(3, 9) = 36$ and uniqueness of $C_{35}(\{1, 7, 11, 16\})$
* [Exoo (1989)](https://doi.org/10.1137/0402043) and [Exoo's 39-vertex matrix](https://cs.indstate.edu/ge/RAMSEY/r3.10.39)
* [Angeltveit (2025), Theorem 1 ($R(3, 10) \le 41$)](https://doi.org/10.37236/12936)
* [Harborth and Krause (2003), Table 1](https://www.researchgate.net/profile/Heiko-Harborth/publication/265670071_Ramsey_numbers_for_circulant_colorings/links/617430c6eef53e51e1d63351/Ramsey-numbers-for-circulant-colorings.pdf) and [Coniglio et al. (`arXiv:2608.18769v1`, Table 8)](https://arxiv.org/html/2608.18769v1#S8.T8)
* [Prior-art audit](../PRIOR_ART.md)
