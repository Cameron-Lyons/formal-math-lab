# Erdős Problem #64: Power-of-Two Cycles

[Erdős Problem #64](https://www.erdosproblems.com/64) (the Erdős–Gyárfás conjecture) asks a deceptively simple question: take any nonempty finite simple graph in which every vertex has at least three neighbors (minimum degree at least three). Must it always contain a simple cycle whose length is a power of two — that is, $4, 8, 16, 32, \ldots$?

The conjecture remains open in general, and no counterexample is known. This folder brings together Lean 4 formalizations, written structural theorems, and reproducible C++/Python searches that push the minimum size of any counterexample to **42 vertices**, pin down what a smallest counterexample must look like, and settle several infinite graph families outright.

| Field | Summary |
| --- | --- |
| Status | Open in general. Every counterexample has at least **42 vertices**. |
| Order bound | A written reduction and a C++ search using nauty exhaust all 103 starting configurations through 41 vertices. See [Order41.md](Order41.md) for the proof and replay commands. |
| Main Lean theorems | `Erdos64.TrianglePacking.liftCycle` doubles the length of a quotient cycle when same-corner visits are isolated. `Erdos64.Terminals.terminalEquivalences` gives two reformulations of the unrestricted conjecture. `Erdos64.cycle_of_P15_plus_isolate_free` settles a forbidden-subgraph case. |
| Verification | Run `lake --wfail build` and `lake env leanchecker --fresh Erdos64` with Lean 4.36.0 and its standard library. See [Verification](#verification). |
| Prior art | Ducoffe and Dumitru verified the conjecture through 40 vertices; Hegde, Sandeep, and Shashank proved it for graphs with no induced $P_{13}$. |

---

## How the pieces in this folder fit together

Throughout these notes, a simple cycle of length $2^k$ ($k \ge 2$) is called a *dyadic cycle*, a graph in which every vertex has degree three is called *cubic*, and a *counterexample* is a nonempty finite simple graph of minimum degree at least three with no dyadic cycle.

* **Exhaustive order bound ([Order41.md](Order41.md)):** Rules out every unrestricted counterexample on at most 41 vertices.
* **Anatomy of a smallest counterexample ([DegreeComponents.md](DegreeComponents.md), [Separators.md](Separators.md), [Bridges.md](Bridges.md)):** Constrains triangles, induced claws, degree-three components, and small vertex/edge cuts.
* **Independent sets and bipartite bounds ([AlgebraicDescent.md](AlgebraicDescent.md), [BipartiteBounds.md](BipartiteBounds.md)):** Uses a cycle-doubling compression trick and $\mathbf{F}_2$ linear algebra to push cubic bipartite counterexamples to at least 136 vertices (150 with an even number of perfect matchings).
* **Structured graph classes ([TreewidthThree.md](TreewidthThree.md), [RecursiveGadgets.md](RecursiveGadgets.md), Lean proofs):** Settles graphs of treewidth at most three, pathwidth at most three, $\{V_8, Q_{10}\}$-minor-free cubic graphs, abelian voltage covers of $K_4$, and graphs forbidding $P_{15} \sqcup K_1$.
* **Reformulations and large constructions ([CounterexampleSearch.md](CounterexampleSearch.md)):** Translates the full conjecture into path-length statements between two boundary terminals and builds an 8,628-vertex cubic graph with no dyadic cycle shorter than 128.

---

## Bounds on unrestricted counterexamples

### Order bound through 41 vertices

On at most 41 vertices, a power-of-two cycle can only have length $4, 8, 16,$ or $32$. A minimal counterexample splits naturally into two exhaustive regimes:

1. **All triangles share one vertex** (or the graph is triangle-free), yielding 67 starting configurations around a chosen center and its neighborhood.
2. **Two triangles are vertex-disjoint**, so we start from a closest pair of disjoint triangles connected by a shortest path of length $r \in \{1, \ldots, 36\}$, yielding 36 starting configurations.

The [reduction and case counts](Order41.md#proof) show that all 103 starting graphs exhaust to zero counterexamples, establishing the **42-vertex** lower bound.

### Structure of a smallest counterexample

Suppose a counterexample exists, and choose one with the fewest vertices, breaking ties by the fewest edges. Two global structural forces immediately take hold:

* **Contracting disjoint triangles:** Collapsing any collection of vertex-disjoint triangles into single vertices shrinks the graph while keeping minimum degree three. When a cycle in the contracted quotient passes through a triangle via two different corners, we can route it across that triangle using either **1 or 2 internal edges**. That extra choice lets us double the quotient cycle's length into a power-of-two cycle in the original graph unless enough uncovered degree-three vertices absorb the parity. Consequently, any set of vertex-disjoint triangles leaves at least two degree-three vertices uncovered, and any counterexample whose vertices partition into triangles has at least **126 vertices**.
* **Forced induced claw:** If a globally minimal counterexample avoided an induced claw ($K_{1,3}$, a center adjacent to three pairwise nonadjacent neighbors), its triangles would interlock so tightly that replacing each triangle by a vertex would give a smaller cubic graph whose power-of-two cycles all lift back to doubled cycles. Every globally minimal counterexample therefore contains an induced claw.

See the [induced-claw proof](DegreeComponents.md#an-induced-claw-in-a-globally-minimal-counterexample), the [triangle contraction proof](DegreeComponents.md#contracting-disjoint-triangles), and the [Lean cycle lift](Erdos64/TrianglePacking.lean).

### Independent sets and cubic bipartite bounds

If every vertex outside an independent set $X$ sees either $0$ or $2$ vertices of $X$, we can *suppress* each degree-two outside vertex — replacing its two-edge path by a single edge directly on $X$. Every cycle in the compressed graph doubles in length when lifted back, so a dyadic-cycle-free graph compresses to a smaller dyadic-cycle-free graph with the same degrees. In a minimum-order counterexample, no nonempty independent set can therefore meet every outside neighborhood in $0$ or $2$ vertices.

For a cubic *bipartite* counterexample (whose vertices split into two independent *shores* of equal size), recording the parity of neighbor counts for every subset of one shore at all but one vertex of the opposite shore forces a collision by the pigeonhole principle. Taking the symmetric difference of the two colliding subsets, suppressing degree-two vertices, and repairing at most one degree drop via a two-copy bridge produces a strictly smaller cubic counterexample. Thus **any smallest cubic counterexample is nonbipartite**.

Push this $\mathbf{F}_2$ linear algebra further — double-counting Hamming distances between columns of the inverse adjacency matrix in the invertible case, and counting edges incident to a kernel vector in the singular case — and the order bounds jump sharply: every cubic bipartite counterexample has at least **136 vertices**, and at least **150 vertices** if it has an even number of perfect matchings. See [AlgebraicDescent.md](AlgebraicDescent.md), [Erdos64/EvenNeighborhood.lean](Erdos64/EvenNeighborhood.lean) for the Lean cycle-doubling and degree-transfer proofs, and [BipartiteBounds.md](BipartiteBounds.md) for the cubic bipartite bounds.

### Treewidth three and excluded minors

A graph has *treewidth at most three* if it sits inside a 3-tree (built from a starting triangle by repeatedly gluing new vertices onto existing triangles). At every order, every graph of treewidth at most three and minimum degree at least three contains a $4$-, $8$-, or $16$-cycle avoiding any chosen edge, and a 34-vertex cubic example proves that $16$ cannot be lowered.

The proof classifies every dyadic-cycle-free piece that can grow behind a three-vertex boundary into just six shapes. Lean checks the resulting finite calculation over 62 ordered boundary profiles, while a C++ program independently checks both the shape classification and the 34-vertex example. For cubic graphs forbidding both the Wagner graph ($V_8$) and the pentagonal prism ($Q_{10}$) as minors, a separate recursive-gadget proof gives the sharp upper bound $32$. See [TreewidthThree.md](TreewidthThree.md), the [Lean finite certificate](Erdos64/TreewidthProfiles.lean), and [RecursiveGadgets.md](RecursiveGadgets.md).

---

## Other graph classes

**Theorem.** Every nonempty simple graph of minimum degree at least three with no induced $P_{15} \sqcup K_1$ contains a simple cycle of length $4$, $8$, or $16$ ([Erdos64.lean](Erdos64.lean)). Here $P_{15}$ is the 15-vertex path and $K_1$ is an extra vertex with no neighbors on the path. In particular, the theorem holds for every $P_{15}$-free graph regardless of order.

Hegde, Sandeep, and Shashank previously proved the $P_{13}$-free case ([arXiv:2410.22842](https://arxiv.org/abs/2410.22842)), and an earlier theorem in this repository covered graphs forbidding an induced $P_{14} \sqcup K_1$. Including the isolated vertex is a strict generalization even at minimum degree three: adding three universal vertices (adjacent to everything) to $P_{14} \sqcup K_1$ keeps that induced pattern while preventing any induced path from having more than 14 vertices.

| Hypothesis | Forced simple cycle lengths | Lean theorem |
| --- | --- | --- |
| No induced $P_{15} \sqcup K_1$, minimum degree at least three | 4, 8, or 16 | [`cycle_of_P15_plus_isolate_free`](Erdos64.lean) |
| Triangle-free, no induced $P_{17} \sqcup K_1$, minimum degree at least three | 4, 8, or 16 | [`cycle_of_triangleFree_P17_plus_isolate_free`](Erdos64/TriangleFree.lean) |
| Finite, pathwidth at most three, minimum degree at least three | 4 or 8 | [`cycle_of_pathwidth_atMost_three`](Erdos64/Pathwidth.lean) |
| Abelian voltage cover of $K_4$ | 4, 8, or 16 | [`TetrahedronCover.cycle_of_abelian_voltage`](Erdos64/TetrahedronCover.lean) |

---

## The unrestricted conjecture

Lean proves that the full conjecture is equivalent to a path-length statement between two boundary vertices ([Erdos64/Terminals.lean](Erdos64/Terminals.lean), discussed in [CounterexampleSearch.md](CounterexampleSearch.md)). Take a finite simple graph with two nonadjacent *terminals* of degree at least two and all other vertices of degree at least three. If the graph has no power-of-two cycle, the conjecture forces two simple paths between those terminals: one of length $2^k$ and another of length $2^j - 1$, for some $k, j \ge 2$. Either requirement by itself, across all such graphs, implies the full conjecture.

Several additional constructions and structural bounds are recorded in this folder:

* **First dyadic cycle at 128:** A connected cubic graph on **8,628 vertices** has shortest power-of-two cycle $128$. The script [scripts/mixed_gadget_graph.py](scripts/mixed_gadget_graph.py) builds it, rules out cycle lengths $4$ through $64$ among powers of two, and checks an explicit 128-cycle edge by edge.
* **Bridges in cubic counterexamples:** An exhaustive search shows that any connected cubic counterexample with a bridge has at least **82 vertices** ([Bridges.md](Bridges.md)).
* **Vertex identification and degree sequences:** For a minimum-order counterexample, Lean checks a path condition for vertex identification ([Erdos64/Identification.lean](Erdos64/Identification.lean)), and counting connected components of degree-three vertices constrains the degree sequence ([DegreeComponents.md](DegreeComponents.md)).
* **Separators at arbitrary maximum degree:** Every connected counterexample contains a subdivision of a 3-connected graph on at least **25 vertices**, of treewidth at least four, with at most one edge subdivided. Allowing arbitrary maximum degree, any connected counterexample has at least **48 vertices** if it has a separating pair, at least **57** if it has a cut vertex, and at least **58** if it has a bridge. See [Separators.md](Separators.md) and the [Lean proof for bipartite pieces](Erdos64/CutVertex.lean).

---

## How the forbidden-induced-path proof works

Assume a graph of minimum degree at least three contains no simple cycle of length $4$, $8$, or $16$. Rather than checking graphs of bounded size, the proof forces an induced $P_{15} \sqcup K_1$ inside *any* host graph, finite or infinite, in two stages:

1. **Force an induced $P_{15}$:** The earlier $P_{14}$-free proof ([Erdos64/PathFree.lean](Erdos64/PathFree.lean)) guarantees an induced $P_{14}$. Assuming no induced $P_{15}$ exists, starting from that $P_{14}$ and systematically exposing new neighbors leads every branch to a contradiction. Hence the host graph must contain an induced $P_{15}$, possibly on a different set of vertices ([Erdos64/Path15.lean](Erdos64/Path15.lean)).
2. **Force an isolated vertex off that path:** Fix an induced $P_{15}$. A second search rules out the possibility that every outside vertex has a neighbor on the path (i.e., that the path *dominates* the graph), forcing some vertex outside the path with no neighbor on it ([Erdos64/DominatingCases.lean](Erdos64/DominatingCases.lean)). Together they induce $P_{15} \sqcup K_1$.

Both searches grow a finite *exposed* induced subgraph one vertex at a time. Whenever an exposed vertex has at most two exposed neighbors, minimum degree three guarantees a fresh neighbor outside the exposed set, and the search branches over all subsets of exposed vertices that could be adjacent to it. Two chosen neighbors cannot already be joined by an exposed simple path of $2$, $6$, or $14$ edges, because the fresh vertex would close a $4$-, $8$-, or $16$-cycle. In the first search, finding an induced $P_{15}$ closes the branch; in the second, every fresh vertex must have at least one neighbor on the fixed $P_{15}$. Lean verifies that every valid host extension is covered and rejects any run that hits its depth limit without a contradiction. See [Erdos64/ExtensionSoundness.lean](Erdos64/ExtensionSoundness.lean), [Erdos64/PathFreeSearch.lean](Erdos64/PathFreeSearch.lean), [Erdos64/LongPath.lean](Erdos64/LongPath.lean), and [Erdos64/Search.lean](Erdos64/Search.lean).

In a triangle-free graph, no two neighbors of the fresh vertex can be adjacent either. Adding that single pruning rule lets the first search force an induced $P_{17}$ and the second rule out a dominating induced $P_{17}$ ([Erdos64/TriangleFreeSearch.lean](Erdos64/TriangleFreeSearch.lean)).

---

## Pathwidth, voltage covers, and claw/net-free graphs

* **Pathwidth at most three:** By [Kinnersley's characterization](https://www.sciencedirect.com/science/article/pii/002001909290234M), a graph has *pathwidth at most three* if its vertices can be lined up so that across every prefix cut, at most three earlier vertices (the *frontier*) still have edges going forward. Adding vertices in this order, every backward edge of a new vertex goes into that frontier of size at most three, and any vertex leaving the frontier must already have degree at least three. An exhaustive check in [Erdos64/Pathwidth.lean](Erdos64/Pathwidth.lean) shows that the graph can neither finish early nor reach eleven vertices without forming a $4$- or $8$-cycle.
* **Abelian voltage covers of $K_4$:** To build an *abelian voltage cover* of $K_4$, label each oriented edge $ij$ of $K_4$ with a "shift" $s_{ij}$ from an abelian group (with $s_{ji} = -s_{ij}$), and create lifted edges $(i, x) \sim (j, x + s_{ij})$ for every group element $x$. Shifting the origin inside each vertex fiber sets the voltages on a spanning tree of $K_4$ to zero, leaving three independent voltages. The proof in [Erdos64/TetrahedronCover.lean](Erdos64/TetrahedronCover.lean) tests fourteen candidate closed walks of total voltage zero: each lifts to a simple cycle unless it repeats a lifted vertex, and every possible repetition imposes a linear equation resolved by case analysis. The bound $16$ is sharp: over $\mathbb{Z}/7\mathbb{Z}$, assigning zero to the three edges out of vertex $0$ and $(1, 3, 2)$ to $(12, 13, 23)$ yields a 28-vertex cubic graph with a $16$-cycle and no $4$- or $8$-cycle, verified by `sevenCover_sharp`.
* **Forbidding both a net and a once-subdivided claw:** The package also includes an elementary Lean proof that forbidding both an induced net (a triangle with a pendant leaf at each corner) and an induced once-subdivided claw forces a $4$-cycle at minimum degree three ([Erdos64/NetAndTripod.lean](Erdos64/NetAndTripod.lean)).

---

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
