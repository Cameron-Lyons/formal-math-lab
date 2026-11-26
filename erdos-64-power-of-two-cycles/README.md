# Erdős Problem #64, power-of-two cycles

[Erdős Problem #64](https://www.erdosproblems.com/64) (due to Erdős and Gyárfás) asks whether every nonempty finite simple graph of minimum degree at least three contains a simple cycle of length $2^k$ for some $k \ge 2$.

| Field | Summary |
| --- | --- |
| Status | Open in general. Every counterexample has at least **42 vertices**. |
| Order bound | A written reduction and a C++ search using nauty exhaust all 103 starting configurations through 41 vertices. See [Order41.md](Order41.md) for the proof and replay commands. |
| Main Lean theorems | `Erdos64.TrianglePacking.liftCycle` doubles the length of a quotient cycle when same-corner visits are isolated. `Erdos64.Terminals.terminalEquivalences` gives two reformulations of the unrestricted conjecture. `Erdos64.cycle_of_P15_plus_isolate_free` settles a forbidden-subgraph case. |
| Verification | Run `lake --wfail build` and `lake env leanchecker --fresh Erdos64` with Lean 4.36.0 and its standard library. See [Verification](#verification). |
| Prior art | Ducoffe and Dumitru verified the conjecture through 40 vertices; Hegde, Sandeep, and Shashank proved it for graphs with no induced $P_{13}$. See the [literature check from 25 November 2026](../PRIOR_ART.md#erdős-64-power-of-two-cycles). |

## Bounds on unrestricted counterexamples

### Order bound through 41 vertices

On at most 41 vertices, a power-of-two cycle must have length 4, 8, 16, or 32. The search splits into two cases: either one vertex hits every triangle, or we start from a closest pair of disjoint triangles together with a shortest path between them. The [reduction and case counts](Order41.md#proof) show that all 103 starting graphs lead to no counterexample.

### Structure of a smallest counterexample

Suppose a counterexample exists, and pick one with the fewest vertices, breaking ties by the fewest edges. Any set of vertex-disjoint triangles leaves at least two degree-three vertices uncovered. Contracting the triangles and lifting cycles (using either one or two edges inside each triangle) yields a contradiction otherwise. As a consequence, any counterexample whose vertices partition into triangles has at least **126 vertices**. A globally minimal counterexample must also contain an induced claw. See the [induced-claw proof](DegreeComponents.md#an-induced-claw-in-a-globally-minimal-counterexample), the [triangle contraction proof](DegreeComponents.md#contracting-disjoint-triangles), and the [Lean cycle lift](Erdos64/TrianglePacking.lean).

### Independent sets and cubic bipartite bounds

In a minimum-order counterexample, no nonempty independent set can meet every outside neighborhood in 0 or 2 vertices. For a cubic bipartite counterexample, record the parity of neighbor counts for subsets of one shore at all but one vertex of the other shore. By the pigeonhole principle two subsets have the same record, and their symmetric difference produces a smaller cubic counterexample once we suppress degree-two vertices and repair at most one degree drop. Thus any smallest cubic counterexample is nonbipartite.

More strongly, every cubic bipartite counterexample has at least **136 vertices**, and at least **150** if it has an even number of perfect matchings. The 136 bound double-counts Hamming distances between columns of the inverse adjacency matrix; the 150 bound counts edges incident to the support of a kernel vector. See [AlgebraicDescent.md](AlgebraicDescent.md), [Erdos64/EvenNeighborhood.lean](Erdos64/EvenNeighborhood.lean) for the Lean cycle-doubling and degree-transfer proofs, and [BipartiteBounds.md](BipartiteBounds.md) for the cubic bipartite bounds.

### Treewidth three and excluded minors

At every order, a graph of treewidth at most three and minimum degree at least three has a 4-, 8-, or 16-cycle avoiding any chosen edge, and a 34-vertex cubic example shows that 16 cannot be lowered. A written proof classifies the possible clean pieces behind a three-vertex boundary into six shapes; Lean checks the resulting finite calculation over 62 ordered profiles, and a C++ program independently checks both the classification and the 34-vertex example. For cubic graphs with no Wagner graph or pentagonal prism minor, a separate proof gives the sharp upper bound 32. See [TreewidthThree.md](TreewidthThree.md), the [Lean finite certificate](Erdos64/TreewidthProfiles.lean), and [RecursiveGadgets.md](RecursiveGadgets.md).

## Other graph classes

**Theorem.** Every nonempty simple graph of minimum degree at least three with no induced $P_{15}\sqcup K_1$ contains a simple cycle of length 4, 8, or 16 ([Erdos64.lean](Erdos64.lean)). Here $P_{15}$ is the 15-vertex path and the extra vertex has no neighbor on it. In particular, the theorem holds for every $P_{15}$-free graph regardless of order.

Hegde, Sandeep, and Shashank proved the $P_{13}$-free case ([arXiv:2410.22842](https://arxiv.org/abs/2410.22842)), and an earlier theorem in this repository covered graphs forbidding an induced $P_{14}\sqcup K_1$ (see the [prior-art audit](../PRIOR_ART.md#erdős-64-power-of-two-cycles)). Adding the isolated vertex is a strict generalization even at minimum degree three: adding three universal vertices to $P_{14}\sqcup K_1$ keeps that induced pattern while bounding every induced path to at most 14 vertices.

| Hypothesis | Forced simple cycle lengths | Lean theorem |
| --- | --- | --- |
| No induced $P_{15}\sqcup K_1$, minimum degree at least three | 4, 8, or 16 | [`cycle_of_P15_plus_isolate_free`](Erdos64.lean) |
| Triangle-free, no induced $P_{17}\sqcup K_1$, minimum degree at least three | 4, 8, or 16 | [`cycle_of_triangleFree_P17_plus_isolate_free`](Erdos64/TriangleFree.lean) |
| Finite, pathwidth at most three, minimum degree at least three | 4 or 8 | [`cycle_of_pathwidth_atMost_three`](Erdos64/Pathwidth.lean) |
| Abelian voltage cover of $K_4$ | 4, 8, or 16 | [`TetrahedronCover.cycle_of_abelian_voltage`](Erdos64/TetrahedronCover.lean) |

## The unrestricted conjecture

Lean proves that the full conjecture is equivalent to a path statement between two terminals ([Erdos64/Terminals.lean](Erdos64/Terminals.lean), discussed in [CounterexampleSearch.md](CounterexampleSearch.md)). Take a finite simple graph with two nonadjacent vertices of degree at least two and all other vertices of degree at least three. If the graph has no power-of-two cycle, the conjecture forces a simple path between those two vertices of length $2^k$ and another of length $2^j-1$, for some $k, j \ge 2$. Either requirement by itself, across all such graphs, implies the full conjecture.

Several additional constructions and structural bounds are recorded in this folder:

* A connected cubic graph on 8,628 vertices has shortest power-of-two cycle 128. The script [scripts/mixed_gadget_graph.py](scripts/mixed_gadget_graph.py) builds it, rules out cycle lengths 4 through 64 among powers of two, and checks a 128-cycle edge by edge.
* An exhaustive search shows that a connected cubic counterexample with a bridge has at least 82 vertices ([Bridges.md](Bridges.md)).
* For a minimum-order counterexample, Lean checks a path condition for vertex identification ([Erdos64/Identification.lean](Erdos64/Identification.lean)), and counting degree-three components constrains the degree sequence ([DegreeComponents.md](DegreeComponents.md)).
* Every connected counterexample contains a subdivision of a 3-connected graph on at least 25 vertices, of treewidth at least four, with at most one edge subdivided. Allowing arbitrary maximum degree, any connected counterexample has at least 48 vertices if it has a separating pair, at least 57 if it has a cut vertex, and at least 58 if it has a bridge. See [Separators.md](Separators.md) and the [Lean proof for bipartite pieces](Erdos64/CutVertex.lean).

## The forbidden induced path proof

Assume a graph of minimum degree at least three has no simple cycle of length 4, 8, or 16. The proof runs in two steps:

1. The earlier $P_{14}$-free proof ([Erdos64/PathFree.lean](Erdos64/PathFree.lean)) forces an induced $P_{14}$. Suppose there is no induced $P_{15}$. Starting from that $P_{14}$, every branch of the extension search reaches a contradiction, so the graph must contain an induced $P_{15}$, possibly on different vertices ([Erdos64/Path15.lean](Erdos64/Path15.lean)).
2. Fix an induced $P_{15}$. A second search rules out this path dominating the rest of the graph, so some vertex outside the path has no neighbor on it ([Erdos64/DominatingCases.lean](Erdos64/DominatingCases.lean)). Together they induce $P_{15}\sqcup K_1$.

Both searches expose one vertex at a time. Whenever an exposed vertex has at most two exposed neighbors, minimum degree three guarantees a fresh neighbor, and the search branches over all subsets of exposed vertices that could be adjacent to it. Two chosen neighbors cannot already be connected by an exposed simple path of 2, 6, or 14 edges, since the fresh vertex would close a 4-, 8-, or 16-cycle. In the first search, finding an induced $P_{15}$ closes the branch; in the second, every fresh vertex must have a neighbor on the fixed $P_{15}$. Lean verifies that every host extension is covered and rejects any run that hits its depth limit without a contradiction. See [Erdos64/ExtensionSoundness.lean](Erdos64/ExtensionSoundness.lean), [Erdos64/PathFreeSearch.lean](Erdos64/PathFreeSearch.lean), [Erdos64/LongPath.lean](Erdos64/LongPath.lean), and [Erdos64/Search.lean](Erdos64/Search.lean).

In a triangle-free graph, no two neighbors of the fresh vertex can be adjacent either. Adding that rule lets the first search reach an induced $P_{17}$ and the second rule out a dominating induced $P_{17}$ ([Erdos64/TriangleFreeSearch.lean](Erdos64/TriangleFreeSearch.lean)).

## Pathwidth and voltage covers

For pathwidth at most three, [Kinnersley's characterization](https://www.sciencedirect.com/science/article/pii/002001909290234M) gives a vertex ordering in which, across every prefix cut, at most three earlier vertices still have neighbors to come. Adding vertices in this order, every backward edge of a new vertex goes to that frontier of size at most three, and any vertex leaving the frontier must already have at least three edges. An exhaustive check in [Erdos64/Pathwidth.lean](Erdos64/Pathwidth.lean) shows that the graph can neither finish earlier nor reach eleven vertices without creating a 4- or 8-cycle.

For an abelian voltage cover of $K_4$, assign an element of an abelian group to each oriented edge, negating it on reversal, and lift each edge $ij$ from $(i, x)$ to $(j, x + s_{ij})$. Shifting the origin in each fiber sets the voltages on a spanning tree to zero. The proof in [Erdos64/TetrahedronCover.lean](Erdos64/TetrahedronCover.lean) checks fourteen candidate closed walks in the three remaining voltages: a walk of total voltage zero lifts to a simple cycle unless it repeats a lifted vertex, and each possible repetition imposes a linear equation handled by case analysis. The bound 16 is sharp: over $\mathbb{Z}/7\mathbb{Z}$, putting zero on the three edges out of vertex 0 and $(1, 3, 2)$ on $(12, 13, 23)$ yields a 28-vertex cubic graph with a 16-cycle and no 4- or 8-cycle, verified by `sevenCover_sharp`.

The package also contains an elementary proof that forbidding both an induced net and an induced once-subdivided claw forces a 4-cycle at minimum degree three ([Erdos64/NetAndTripod.lean](Erdos64/NetAndTripod.lean)).

## Verification

Run these commands from this directory with the pinned Lean 4.36.0 toolchain:

```sh
lake --wfail build
lake env leanchecker --fresh Erdos64
```

The default target imports all Lean proofs in the package. Trust boundaries break down as follows:

* Lean's kernel checks the triangle cycle lift, the terminal equivalences, and the symbolic voltage-cover proof.
* The forbidden-path, pathwidth, and treewidth-profile proofs rely on `native_decide` for finite checks and therefore trust Lean's compiler for those evaluations.
* The full [packing argument](DegreeComponents.md#contracting-disjoint-triangles) and the reduction from treewidth-three graphs to profiles in [TreewidthThree.md](TreewidthThree.md) are written proofs.
* The unrestricted order-41 bound relies on the external C++ enumeration documented in [Order41.md](Order41.md#reproduction).

To reproduce the forbidden-path search counts independently, compile and run the C++23 checker:

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

The checker also reruns the earlier dominating $P_{14}$ search (121,786 partial graphs) and exits with a nonzero status if any branch stays unresolved. These counts measure only the search tree; the resulting theorems hold for host graphs of arbitrary order.
