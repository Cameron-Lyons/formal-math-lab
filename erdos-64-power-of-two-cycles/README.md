# Erdős Problem #64, power-of-two cycles

Erdős and Gyárfás ask whether every nonempty finite simple graph of minimum degree at least three contains a simple cycle of length $2^k$ for some $k\ge 2$. [Erdős Problem #64](https://www.erdosproblems.com/64)

| Field | Summary |
| --- | --- |
| Status | Open in general. Every counterexample has at least **42 vertices**. |
| Order bound | A written reduction and a C++ search using nauty exhaust all 103 starting configurations through 41 vertices. [Proof and replay commands](Order41.md) |
| Main Lean theorems | `Erdos64.TrianglePacking.liftCycle` doubles the length of a quotient cycle when same-corner visits are isolated. `Erdos64.Terminals.terminalEquivalences` gives two reformulations of the unrestricted conjecture. `Erdos64.cycle_of_P15_plus_isolate_free` proves a forbidden-subgraph case. |
| Verification | `lake --wfail build` and `lake env leanchecker --fresh Erdos64` with Lean 4.36.0 and its standard library. [Verification details](#verification) |
| Prior art | Ducoffe and Dumitru verified the conjecture through 40 vertices. Hegde, Sandeep and Shashank proved it for graphs with no induced $P_{13}$. [Literature checked 25 November 2026](../PRIOR_ART.md#erdős-64-power-of-two-cycles) |

## Bounds on unrestricted counterexamples

**Order bound.** On at most 41 vertices the cycle must have length 4, 8, 16 or 32. The search has two cases. Either one vertex meets every triangle, or a closest pair of disjoint triangles and a shortest path between them give the starting graph. [Reduction and case counts](Order41.md#proof)

**Structure of a smallest counterexample.** Suppose a counterexample exists. Choose one with the fewest vertices, breaking ties by the number of edges. Every collection of vertex-disjoint triangles leaves at least two degree-three vertices uncovered. The proof contracts the triangles and lifts cycles by using either one edge or two inside a triangle. A counterexample whose entire vertex set can be partitioned into triangles must have at least **126 vertices**. A globally minimal counterexample also contains an induced claw. [Induced-claw proof](DegreeComponents.md#an-induced-claw-in-a-globally-minimal-counterexample) · [Triangle contraction proof](DegreeComponents.md#contracting-disjoint-triangles) · [Lean cycle lift](Erdos64/TrianglePacking.lean)

A nonempty independent set in a minimum-order counterexample cannot meet every outside neighborhood in zero or two vertices. For a cubic bipartite counterexample, compare the parity records of subsets of one shore at all but one vertex of the other shore. Two subsets have the same record, and their symmetric difference gives a smaller cubic counterexample after suppressing vertices of degree two and repairing at most one degree. Hence a smallest cubic counterexample is nonbipartite. A cubic bipartite counterexample has at least **136 vertices**, and at least **150** if its number of perfect matchings is even. The first bound counts the distances between inverse columns two ways. The even-matching case follows by counting edges incident to a kernel vector’s support. [Algebraic descent](AlgebraicDescent.md) · [Lean cycle-doubling and degree transfer](Erdos64/EvenNeighborhood.lean) · [Cubic bipartite order bounds](BipartiteBounds.md)

At every order, a graph of treewidth at most three and minimum degree at least three has a 4-, 8- or 16-cycle avoiding any prescribed edge. A 34-vertex cubic graph shows that 16 is necessary. A hand proof classifies the pieces at a three-vertex boundary into six shapes. Lean checks the resulting finite calculation on 62 ordered profiles, and C++ checks the classification and the example independently. For cubic graphs excluding the Wagner graph and pentagonal prism as minors, a separate proof gives the sharp upper bound 32. [Treewidth proof and example](TreewidthThree.md) · [Lean finite certificate](Erdos64/TreewidthProfiles.lean) · [Cubic minor and substitution results](RecursiveGadgets.md)

## Other graph classes

**Theorem.** Every nonempty simple graph of minimum degree at least three with no induced copy of $P_{15}\sqcup K_1$ contains a simple cycle of length 4, 8, or 16. Here $P_{15}$ is the path on fifteen vertices, and the extra vertex has no neighbor on the path. In particular the result applies to every $P_{15}$-free graph, with no bound on its order. [Lean theorem](Erdos64.lean)

Hegde, Sandeep and Shashank proved the $P_{13}$-free case. The preceding result in this repository covered graphs forbidding an induced $P_{14}\sqcup K_1$. The additional vertex gives a strict extension even at minimum degree three. For example, add three universal vertices to $P_{14}\sqcup K_1$. The original pattern remains induced, and every induced path has at most fourteen vertices. [Paper](https://arxiv.org/abs/2410.22842) · [Prior-art audit](../PRIOR_ART.md#erdős-64-power-of-two-cycles)

| Hypothesis | Forced simple cycle lengths | Lean theorem |
| --- | --- | --- |
| No induced $P_{15}\sqcup K_1$, minimum degree at least three | 4, 8, or 16 | [`cycle_of_P15_plus_isolate_free`](Erdos64.lean) |
| Triangle-free, no induced $P_{17}\sqcup K_1$, minimum degree at least three | 4, 8, or 16 | [`cycle_of_triangleFree_P17_plus_isolate_free`](Erdos64/TriangleFree.lean) |
| Finite, pathwidth at most three, minimum degree at least three | 4 or 8 | [`cycle_of_pathwidth_atMost_three`](Erdos64/Pathwidth.lean) |
| Abelian voltage cover of $K_4$ | 4, 8, or 16 | [`TetrahedronCover.cycle_of_abelian_voltage`](Erdos64/TetrahedronCover.lean) |

## The unrestricted conjecture

Lean proves that the full conjecture is equivalent to a terminal-path statement. Consider two nonadjacent vertices of degree at least two in a finite simple graph, with degree at least three elsewhere. If the graph contains no power-of-two cycle, the conjecture would force a simple path between these vertices of length $2^k$, and another of length $2^j-1$, for $k,j\ge2$. Either path requirement alone, applied to all such graphs, implies the full conjecture. [Lean equivalences](Erdos64/Terminals.lean) · [Proof and counterexample search](CounterexampleSearch.md)

A separate construction gives a connected cubic graph on 8,628 vertices whose shortest power-of-two cycle has length 128. An explicit program reconstructs the graph, excludes lengths 4 through 64 among powers of two, and checks a 128-cycle edge by edge. An exhaustive search proves that a connected cubic counterexample with a bridge has at least 82 vertices. For a minimum-order counterexample there is also a Lean-verified path condition for vertex identification. Counting components of degree-three vertices gives additional constraints on its degree sequence. [Construction](scripts/mixed_gadget_graph.py) · [Edge-cut bounds](Bridges.md) · [Vertex identification](Erdos64/Identification.lean) · [Degree bounds](DegreeComponents.md)

Every connected counterexample contains a subdivision of a 3-connected graph on at least 25 vertices, of treewidth at least four, with at most one edge subdivided. A counterexample with a separating pair of vertices has at least 48 vertices, one with a cut vertex at least 57, and one with a bridge at least 58, assuming connectivity. These bounds allow arbitrary maximum degree. [Separator reduction and finite bounds](Separators.md) · [Lean proof for bipartite pieces](Erdos64/CutVertex.lean)

## The forbidden induced path proof

Suppose there is no simple cycle of length 4, 8, or 16.

1. The existing $P_{14}$-free result forces an induced $P_{14}$. Assume the graph has no induced $P_{15}$. Starting from the $P_{14}$, every possible branch of the extension search gives a contradiction. Thus the graph contains an induced $P_{15}$, possibly on different vertices. [Previous step](Erdos64/PathFree.lean) · [Fourteen-to-fifteen step](Erdos64/Path15.lean)
2. Choose an induced $P_{15}$. A second search shows that it cannot dominate the graph. Hence some vertex outside the path has no neighbor on it. The path and this vertex induce $P_{15}\sqcup K_1$. [Dominating-path proof](Erdos64/DominatingCases.lean)

Both searches expose one vertex at a time. If a vertex has at most two exposed neighbors, the minimum degree guarantees a fresh neighbor. The search branches over its possible neighbors among **all** exposed vertices. Two of those neighbors cannot be the ends of an exposed simple path of 2, 6, or 14 edges, since the fresh vertex would close a forbidden cycle. In the first search, an induced path of fifteen vertices closes a branch. In the second, the fresh vertex must meet the distinguished path. Lean verifies that every possible host extension is covered. A depth limit reached without a contradiction returns failure. [Extension soundness](Erdos64/ExtensionSoundness.lean) · [Longest-path search](Erdos64/PathFreeSearch.lean) · [Branch selection](Erdos64/LongPath.lean) · [Dominating-path search](Erdos64/Search.lean)

In a triangle-free graph, two neighbors of the fresh vertex also cannot be adjacent. Adding this rule lets the first search reach an induced $P_{17}$ and the second rule out a dominating induced $P_{17}$. [Triangle-free search](Erdos64/TriangleFreeSearch.lean)

## Pathwidth and voltage covers

For pathwidth at most three, order the vertices so that across every cut at most three earlier vertices have a neighbor still to come. Add vertices in this order. All backward edges of a new vertex go to this set of at most three. When a vertex leaves the set, all its neighbors have appeared, so at least three incident edges must already be present. An exhaustive check rules out termination at any smaller order or continuation to eleven vertices without producing a 4- or 8-cycle. Lean uses this vertex-order characterization of pathwidth. [Proof](Erdos64/Pathwidth.lean) · [Kinnersley's equivalence with path decompositions](https://www.sciencedirect.com/science/article/pii/002001909290234M)

For a voltage cover, assign an element of an abelian group to each oriented edge of $K_4$, negating the element on edge reversal. An edge $ij$ lifts from $(i,x)$ to $(j,x+s_{ij})$. Changing the origin in each fiber sets three spanning-tree voltages to zero. The proof checks fourteen candidate closed walks in the three remaining voltages. A walk of total voltage zero lifts to a simple cycle unless it repeats a lifted vertex. Each possible repetition imposes a linear equation among the voltages, and the proof checks the resulting cases. The bound 16 is sharp. Over $\mathbb{Z}/7\mathbb{Z}$, assign zero to the three edges out of vertex 0 and assign voltages $(1,3,2)$ on $(12,13,23)$. The resulting 28-vertex cubic graph has a 16-cycle and has neither a 4-cycle nor an 8-cycle, as verified by `sevenCover_sharp`. [Lean proof, walks and sharpness example](Erdos64/TetrahedronCover.lean)

The package also includes an elementary proof that forbidding both an induced net and an induced once-subdivided claw forces a 4-cycle at minimum degree three. [Elementary proof](Erdos64/NetAndTripod.lean)

## Verification

Run the following from this directory with the pinned Lean 4.36.0 toolchain.

```sh
lake --wfail build
lake env leanchecker --fresh Erdos64
```

The default target imports the package's Lean proofs. The kernel checks the triangle cycle lift, terminal equivalences and symbolic voltage-cover proof. The forbidden-path, pathwidth and treewidth-profile proofs use `native_decide` for finite evaluations and trust Lean's compiler for those evaluations. The full packing argument and the reduction from graphs of treewidth three to profiles are written proofs. The unrestricted order bound relies on the external C++ enumeration. [Packing argument](DegreeComponents.md#contracting-disjoint-triangles) · [Treewidth proof](TreewidthThree.md) · [Order-41 replay](Order41.md#reproduction)

To reproduce the forbidden-path counts independently, compile and run the C++23 checker.

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror scripts/pfree_check.cpp -o /tmp/erdos64-pfree-check
/tmp/erdos64-pfree-check
```

| Independent search | Partial graphs examined |
| --- | ---: |
| Longest-path cases $P_2$ through $P_{13}$ | 525,217 |
| Longest-path case $P_{14}$ forcing $P_{15}$ | 580,562 |
| Dominating $P_{15}$ | 214,585 |
| Triangle-free longest-path cases $P_1$ through $P_{16}$ | 177,803 |
| Triangle-free dominating $P_{17}$ | 104,690 |

The checker also reruns the preceding dominating $P_{14}$ case (121,786 partial graphs). It exits unsuccessfully on any unresolved branch. These counts measure the work of the proof. Its conclusions hold for host graphs of arbitrary order.
