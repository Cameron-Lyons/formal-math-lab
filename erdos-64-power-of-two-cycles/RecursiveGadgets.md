# Power-of-Two Cycles Under Recursive Vertex Replacement

Imagine starting with a small cubic graph (at most $14$ vertices) and repeatedly inflating any vertex into a small three-port "gadget" (at most $13$ vertices, with three degree-two ports where the three incident edges plug in). Repeating this operation arbitrarily many times generates cubic graphs of unbounded size — yet **every** graph produced this way must contain a simple cycle of length **4, 8, 16, or 32**, and $32$ is best possible.

Because splitting along $3$-edge cuts decomposes any cubic graph that avoids two small forbidden minors — the $8$-vertex Wagner graph $V_8$ and the $10$-vertex pentagonal prism $Q_{10}$ — into small cyclically $4$-edge-connected pieces, this recursive closure automatically settles the entire $\{V_8, Q_{10}\}$-minor-free cubic class (including every cubic graph of treewidth at most three) with the exact sharp bound $32$.

**Theorem.** Start with any connected simple cubic graph on at most $14$ vertices. Replace any vertex by a connected simple graph on at most $13$ vertices that has three distinct degree-two vertices and all other vertices cubic, attaching the three incident edges of the replaced vertex to the three degree-two vertices by any bijection. Repeat this finitely many times, including at vertices created by earlier steps. Every graph produced this way has a simple cycle of length **4, 8, 16, or 32**, and the bound $32$ is sharp.

This graph family has unbounded order. The theorem follows by induction from a finite computation in Python using nauty.

---

## The five possible clean pieces

A *piece* carries three boundary half-edges: the unchanged single vertex carries all three, while every other primitive piece has one half-edge attached to each of its three degree-two vertices (*ports*). When a vertex inside a piece is replaced, its boundary half-edges participate in the port bijection just like internal edges. Call a piece *clean* if it contains no cycle of length $4, 8, 16,$ or $32$.

**Classification of clean pieces.** Up to permuting the three boundary half-edges, the **only** clean pieces this recursion can build are:

1. the unchanged single vertex,
2. the triangle ($3$ vertices),
3. $H'_7$ ($7$ vertices): $K_4$ with the three edges incident to one vertex subdivided once each,
4. $H_7$ ($7$ vertices): a triangle with two of its vertices expanded into triangles,
5. $H_{15}$ ($15$ vertices): a triangle with two of its vertices replaced by copies of $H_7$, with their distinguished ports facing outward.

The last three come from Garcia's library ([Garcia, Sections 3 and 6](https://arxiv.org/html/2609.04686v1#S3)), and these recursive descriptions also verify that all five arise within the order-$13$ replacement limit.

### Transit intervals

When a cycle enters a piece through one port, follows a simple path inside the piece to a second port, and leaves along the departing edge, how many edges does that traversal add? For each pair of ports (equivalently, each choice of the *omitted* third port), list all possible internal simple path lengths plus $1$ for the departing edge. For all five clean pieces, these *transit lengths* fill a single contiguous integer interval:

| Piece | First | Second | Third |
| --- | --- | --- | --- |
| Vertex | $[1,1]$ | $[1,1]$ | $[1,1]$ |
| Triangle | $[2,3]$ | $[2,3]$ | $[2,3]$ |
| $H_7$ | $[4,7]$ | $[3,7]$ | $[3,7]$ |
| $H'_7$ | $[3,7]$ | $[3,7]$ | $[3,7]$ |
| $H_{15}$ | $[6,15]$ | $[4,15]$ | $[4,15]$ |

Across the five pieces there are **$1 + 1 + 3 + 1 + 3 = 9$ distinct oriented interval triples** (the single vertex, triangle, and $H'_7$ are symmetric in all three ports, while $H_7$ and $H_{15}$ have one distinguished port and allow swapping their two symmetric branches).

---

## Induction and finite verification

**The big idea.** Think of a recursive expansion as a rooted tree: an unexpanded vertex is a leaf, and each internal node consists of the primitive *core* used for its first replacement together with the child pieces substituted at the core's vertices. Because the parent preserves every edge of every child, any forbidden cycle inside a child survives in the parent. If every child is clean, induction reduces each child to one of the $9$ oriented library triples — collapsing an arbitrarily deep tree into a finite check over cores of order at most $13$ (and root cores of order at most $14$).

Any simple cycle crossing between children crosses each visited child's three-edge boundary an even number of times (hence exactly twice), so it projects to a simple cycle in the core. Conversely, any simple core cycle lifts back by choosing a port-to-port path independently inside each visited child, attaining the entire integer interval obtained by summing the table intervals along the cycle.

The checkers [scripts/gadget_csp.py](scripts/gadget_csp.py) and [scripts/recursive_gadgets.py](scripts/recursive_gadgets.py) enumerate all core cycles, search over oriented labelings, and discard any assignment as soon as some core cycle's summed interval hits $4, 8, 16,$ or $32$. For every surviving assignment, the code constructs the expanded graph explicitly, confirms cleanness by simple-cycle enumeration, and verifies graph isomorphism to one of the five library pieces by exhaustive search for an adjacency-preserving bijection (in every nontrivial piece, the ports are precisely the degree-two vertices, so any graph isomorphism preserves the port set).

| Three-port core order | Connected simple cores | Clean oriented assignments | Largest clean expansion |
| ---: | ---: | ---: | ---: |
| 3 | 1 | 7 | 15 |
| 5 | 2 | 6 | 15 |
| 7 | 10 | 5 | 15 |
| 9 | 63 | 4 | 15 |
| 11 | 482 | 4 | 15 |
| 13 | 4,541 | 2 | 15 |

Counts are per representative core, with incidences ordered by increasing neighbor index and the free half-edge listed last at each degree-two vertex. This proves closure under the induction step. At the root, the checker tests all $621$ connected simple cubic cores of orders $4$ through $14$ and confirms that every oriented assignment creates a $4$-, $8$-, $16$-, or $32$-cycle.

To reproduce the table and root check from this directory, put `geng` from [nauty 2.9.3](https://pallini.di.uniroma1.it/) on `PATH` and run:

```sh
python scripts/recursive_gadgets.py
```

### Why 32 is sharp (a 90-vertex example)

Orient a Hamiltonian $6$-cycle in $K_{3,3}$ and place a copy of $H_{15}$ at each of its $6$ vertices ($6 \cdot 15 = 90$ vertices), aligning each copy's *distinguished* port (the one whose omission gives transit interval $[6, 15]$) with its outgoing edge on the $6$-cycle.

* **4-cycles in $K_{3,3}$:** Any $4$-cycle in $K_{3,3}$ must miss the outgoing $6$-cycle edge of at least one of its vertices (any nonempty vertex set closed under successors contains the entire $6$-cycle). At each vertex where the outgoing edge is missed, the cycle traverses the two outer ports of $H_{15}$, contributing $[6, 15]$ instead of $[4, 15]$. Thus the $4$-cycle's transit-sum interval has lower endpoint between $4 \cdot 4 + 2 = 18$ and $4 \cdot 6 = 24$ and upper endpoint $4 \cdot 15 = 60$ — missing $4, 8, 16$ and capturing $32$.
* **6-cycles in $K_{3,3}$:** Every $6$-cycle has lower endpoint at least $6 \cdot 4 = 24$ (missing $4, 8, 16$).

Together with the internal cleanness of $H_{15}$, this gives a 90-vertex cubic graph whose shortest dyadic cycle has length $32$.

---

## Cubic graphs of treewidth at most three and $\{V_8, Q_{10}\}$-minor-free graphs

**Corollary.** Every finite simple cubic graph with neither the $8$-vertex Wagner graph $V_8$ nor the pentagonal prism $Q_{10}$ as a minor contains a cycle of length $4, 8, 16,$ or $32$. In particular, this holds for every finite simple cubic graph of treewidth at most three, because $V_8$ and $Q_{10}$ are forbidden minors for treewidth three ([Arnborg, Proskurowski, and Corneil](https://doi.org/10.1016/0012-365X(90)90292-P)).

The proof proceeds in three stages: decomposing $3$-edge-connected cubic graphs along $3$-edge cuts, proving a stronger "avoiding a chosen edge" version by induction, and reducing graphs with $1$- or $2$-edge cuts to a minimal $3$-edge-connected piece.

### Stage 1: Splitting along three-edge cuts

Let $H$ be a simple $3$-edge-connected cubic graph, and consider a nontrivial $3$-edge cut (at least two vertices on each side):

* **Connected shores and matching cut:** Both shores are connected (a disconnected shore would have two components each requiring at least $3$ cut edges), and the cut is a matching (moving a vertex incident to two cut edges to the other side would create a smaller cut). A shore on $r \ge 3$ vertices has $(3r - 3)/2 \ge r$ internal edges and therefore contains a cycle. Contracting either shore to a single vertex and deleting loops yields a smaller simple $3$-edge-connected cubic minor, since every cut in the contracted graph lifts to a cut of the same size in $H$.
* **3-vertex-connectivity:** Every simple $3$-edge-connected cubic graph is also $3$-vertex-connected. Deleting one vertex or two adjacent vertices leaves components whose combined edge boundary is at most $4$, contradicting $3$-edge-connectivity. Deleting two nonadjacent vertices $u, v$ leaves at least two components, each needing $3$ boundary edges; both $u$ and $v$ must attach to both components (neither is a cut vertex), so moving $u$ into the component containing two of its neighbors produces a $2$-edge cut.
* **Small terminal graphs:** Repeatedly splitting along nontrivial $3$-edge cuts terminates at *cyclically $4$-edge-connected* cubic graphs (no $3$-edge cut with cycles on both sides). Every such graph of order at least $10$ has a cyclically $4$-edge-connected cubic minor on $10$ vertices: any larger one is built from a smaller one by subdividing two nonadjacent edges and joining the new vertices (so the smaller graph is a minor). There are only five cyclically $4$-edge-connected cubic graphs of order $10$: $Q_{10}$ itself, and four graphs built from $V_8$ by one such edge addition ([Kingan and Kingan, Theorem 2.1, Figure 5, and Section 4](https://www.tandfonline.com/doi/pdf/10.1080/09728600.2024.2333397)). Excluding $V_8$ and $Q_{10}$ therefore forces every terminal graph in the splitting tree to have **order at most 8**.
* **Marked-vertex reassembly:** Fix any vertex $z$ of $H$. By induction on $|V(H)|$, we can reassemble $H$ from a terminal cubic core using our recursive vertex replacements while keeping $z$ unexpanded: at a split, let $J$ be the contraction minor keeping $z$ and let $y$ be the vertex representing the opposite shore; build $J$ with $z$ unexpanded, build the opposite minor with its contraction vertex unexpanded, delete that contraction vertex, and plug the resulting three-port piece into $y$. By simplicity and $3$-vertex-connectivity, deleting the contraction vertex from its initial core leaves a connected primitive with three distinct degree-two vertices, inside which all subsequent replacements occur.

*(Applying the exact same reassembly with root cap $14$ and primitive cap $13$ extends the recursive theorem to every $3$-edge-connected simple cubic graph that has no cyclically $4$-edge-connected cubic minor on $16$ or more vertices.)*

### Stage 2: Avoiding a specified edge

Take any $3$-edge-connected cubic graph $H$ in the $\{V_8, Q_{10}\}$-minor-free class, assign a clean library piece to every vertex, and pick any core edge $e$. We prove by induction on $|V(H)|$ that the expanded graph contains a $4$-, $8$-, $16$-, or $32$-cycle **avoiding the edge corresponding to $e$**:

* **No nontrivial 3-edge cut:** Then $|V(H)| \le 8$, and $H - e$ is connected with two degree-two vertices and all other vertices cubic. The checker tests all such cores ($1$ at order $4$, $4$ at order $6$, and $19$ at order $8$, with the two free half-edges representing the removed edge $e$) and confirms that every clean labeling produces a target cycle.
* **A nontrivial 3-edge cut misses $e$:** The expanded shore disjoint from $e$ is a recursively built three-port piece (via marked-vertex reassembly followed by the given clean vertex substitutions). If it contains a target cycle, we are done. Otherwise, finite closure identifies it with one of the five clean library pieces up to port permutation; replacing that shore by a single vertex with that label in the smaller contraction minor lets us apply the induction hypothesis to $e$.
* **A nontrivial 3-edge cut contains $e$:** Both expanded shores are recursively built three-port pieces. If either contains a target cycle, we are done. Otherwise both are nontrivial clean library pieces, so each has a transit interval in $\{[2,3],\, [3,7],\, [4,7],\, [4,15],\, [6,15]\}$ between the other two cut edges. Joining arbitrary port-to-port paths across those two cut edges attains the sum of the two intervals, and checking endpoints directly confirms that every pairwise sum in this set contains $4$, $8$, or $16$ — giving a target cycle avoiding $e$.

### Stage 3: Reducing cuts of size one or two

Now let $G$ be a connected cubic $\{V_8, Q_{10}\}$-minor-free graph of edge-connectivity at most two. If $G$ has bridges, delete them and let $B$ be a leaf component (bridgeless, attached to the rest of $G$ by a single bridge); otherwise set $B = G$. Inside $B$, choose a nonempty vertex set $A$ of **minimum order** whose edge boundary in $G$ has size $1$ or $2$ (the entire leaf component $B$ is eligible when $G$ has bridges, and either side of a $2$-edge cut is eligible when $B = G$). By minimality, $G[A]$ is connected.

* **Boundary of size two:** The endpoints $x, y \in A$ of the two cut edges are distinct and nonadjacent: a shared endpoint could be dropped from $A$ to leave a smaller eligible set, and adjacent endpoints could both be dropped (leaving a nonempty set because $G$ is simple and cubic). Both cut edges lie inside $B$ (any proper subset of a bridgeless $B$ has at least two boundary edges inside $B$, whereas $B$ has only one edge leaving it). Also $B - A$ is connected, since each of its components needs at least two boundary edges in $B$. Hence there is an $x$-$y$ path outside $A$; contracting that exterior path to a single edge $e = xy$ added to $G[A]$ yields a simple cubic minor $H$ of $G$.
* **Boundary of size one:** Let $r \in A$ be the vertex incident to the unique cut edge, and let $p, q$ be its two neighbors inside $A$. Then $p$ and $q$ are nonadjacent — otherwise removing $\{r, p, q\}$ from $A$ would leave a smaller nonempty set with boundary size two. Suppressing $r$ (deleting $r$ and adding $e = pq$) yields a simple cubic minor $H$ of $G$.

In either case, $H$ is **$3$-edge-connected**: if $H$ had a cut of size at most two, picking a shore avoiding both endpoints of $e$ when they lie on the same side (or either shore when $e$ crosses the cut) would give a proper subset of $A$ with the same boundary size in $G$, contradicting minimality. Because $H$ is a minor of $G$, it still excludes $V_8$ and $Q_{10}$. Applying Stage 2 (with every vertex unexpanded) yields a target cycle in $H - e \subseteq G[A]$, proving the corollary.

### Sharpness in the $\{V_8, Q_{10}\}$-minor-free class

The 90-vertex example above also shows that $32$ is sharp in the $\{V_8, Q_{10}\}$-minor-free class. Every minor model of a cubic graph reduces to a subdivision (connect the at most three attachments in each branch set by a tree and suppress degree-two vertices). Suppose a graph formed by replacing a vertex with a triangle contains a subdivision of $V_8$ or $Q_{10}$. The triangle holds at most three branch vertices, with at least two outside:

* If it held two or more branch vertices, its three boundary edges would separate two sets of at least two branch vertices, contradicting cyclic $4$-edge-connectivity of $V_8$ and $Q_{10}$.
* If it holds one branch vertex, the three subdivided edge paths leaving it must use all three distinct boundary edges; if it holds none, at most one path segment passes through the triangle (each passage uses two of its three boundary edges).

In both surviving cases, contracting the triangle back to a vertex preserves the subdivision (after suppressing extra degree-two vertices). Because the 90-vertex graph is built from $K_{3,3}$ solely via repeated triangle replacements, any $V_8$ or $Q_{10}$ minor would already appear in $K_{3,3}$ — impossible, since $K_{3,3}$ has only $6$ vertices.

---

## An unrestricted-base criterion

Even on an *arbitrarily large* cubic base graph (with no minor restriction at all), putting enough large gadgets $H_7, H'_7, H_{15}$ forces a dyadic cycle via a slick probabilistic argument over the binary cycle space.

**Proposition.** Take any connected bridgeless cubic core, and let $c_0, c_T, c_7, c'_7, c_{15}$ count the vertices assigned to each of the five library pieces (unchanged vertex, triangle, $H_7$, $H'_7$, $H_{15}$). The expanded graph contains a dyadic cycle whenever

$$
c_7 + 3c'_7 + 17c_{15} \ge 3(c_0 + c_T).
$$

**Proof.** Any integer interval $[A, B]$ with $A \ge 3$ and $B \ge 2A$ must contain a power of two at least $4$ (the smallest power of two $\ge A$ is at least $4$ and strictly less than $2A \le B$). Motivated by this, assign each transit interval $[a, b]$ the additive weight $b - 2a$. Across the three port pairs of each piece, the three transit weights sum to:

* **Vertex** ($[1,1] \times 3$): $3(1 - 2) = -3$,
* **Triangle** ($[2,3] \times 3$): $3(3 - 4) = -3$,
* **$H_7$** ($[4,7], [3,7], [3,7]$): $(7 - 8) + (7 - 6) + (7 - 6) = +1$,
* **$H'_7$** ($[3,7] \times 3$): $3(7 - 6) = +3$,
* **$H_{15}$** ($[6,15], [4,15], [4,15]$): $(15 - 12) + (15 - 8) + (15 - 8) = +17$.

Pick a uniformly random element of the binary cycle space of the core (the $\mathbb{F}_2$-vector space of edge subsets having even degree at every vertex). At any vertex $v$, the chosen incident edges form either the empty set or one of the three pairs of incident edges. Restricting the cycle space to the three edges at $v$ gives a linear subspace of the two-dimensional even-parity subspace of $\mathbb{F}_2^3$. Because the core is bridgeless, every edge lies in some cycle; any proper subspace would force one coordinate to be identically zero, so the restriction is surjective and each of the four local states occurs with exact probability $1/4$.

By linearity of expectation, the expected total weight of a random even subgraph is

$$
\frac{1}{4}\bigl(c_7 + 3c'_7 + 17c_{15} - 3(c_0 + c_T)\bigr) \ge 0.
$$

Every nonempty even subgraph of a cubic graph decomposes into vertex-disjoint simple cycles (whose weights simply add up), and the empty subgraph has weight $0$. Because at least one nonempty even subgraph exists, if every simple cycle had strictly negative weight then the expectation would be strictly negative. Some simple cycle therefore has total weight $B - 2A \ge 0$, where $[A, B]$ is its transit interval. Since every simple cycle has length at least $3$ (so $A \ge 3$), its transit interval $[A, B]$ captures a power of two at least $4$. $\square$

### Cores with bridges using only $H_7, H'_7, H_{15}$

In particular, **every expansion of an arbitrary connected simple cubic core using only $H_7, H'_7, H_{15}$ contains a dyadic cycle, even if the core has bridges**.

Delete all bridges of the core and pick a leaf component of the resulting component tree. Its single attachment vertex has degree $2$ in the leaf component, while all other vertices (at least $2$ of them) have degree $3$ and every internal edge lies on a cycle. In a uniform random element of the leaf component's binary cycle space, the unique pair at the degree-$2$ vertex is used with probability $1/2$ and has weight at least $-1$ (contributing at least $-1/2$ in expectation), while each of the at least two degree-$3$ vertices contributes at least $+1/4$. The total expectation is again nonnegative, so the same argument forces a dyadic cycle inside the leaf component.
