# Power-of-two cycles under recursive vertex replacement

**Theorem.** Start with any connected simple cubic graph on at most 14 vertices. Replace any vertex by a connected simple graph on at most 13 vertices that has three distinct degree-two vertices and all other vertices cubic, attaching the three incident edges of the replaced vertex to the three degree-two vertices by any bijection. Repeat this finitely many times, including at vertices created by earlier steps. Every graph produced this way has a simple cycle of length **4, 8, 16, or 32**, and the bound 32 is sharp.

This graph family has unbounded order. The theorem follows by induction from a finite computation in Python using nauty.

## The five possible pieces

A piece carries three boundary half-edges: the unchanged single vertex carries all three, and every other primitive piece has one half-edge at each of its three degree-two vertices. When a vertex of a piece is replaced, its boundary half-edges participate in the port bijection just like internal edges. Call a piece *clean* if it contains no cycle of length 4, 8, 16, or 32.

Up to permuting the three boundary half-edges, the only clean pieces this recursion can build are the unchanged vertex, the triangle, $H_7$, $H'_7$, and $H_{15}$. The last three come from Garcia's library ([Garcia, Sections 3 and 6](https://arxiv.org/html/2609.04686v1#S3)):

* $H'_7$ is $K_4$ with the three edges incident to one vertex subdivided once each.
* $H_7$ is obtained from a triangle by expanding two of its vertices into triangles.
* $H_{15}$ is obtained from a triangle by replacing two of its vertices with copies of $H_7$, with their distinguished ports facing outward.

These constructions also show that all five pieces arise within the order-13 limit.

For each pair of ports, list all possible lengths of a simple path between them, adding 1 for a departing edge. For all five pieces, these values form a single integer interval. The three columns correspond to the three choices of omitted port, up to permutation:

| Piece | First | Second | Third |
| --- | --- | --- | --- |
| Vertex | $[1,1]$ | $[1,1]$ | $[1,1]$ |
| Triangle | $[2,3]$ | $[2,3]$ | $[2,3]$ |
| $H_7$ | $[4,7]$ | $[3,7]$ | $[3,7]$ |
| $H'_7$ | $[3,7]$ | $[3,7]$ | $[3,7]$ |
| $H_{15}$ | $[6,15]$ | $[4,15]$ | $[4,15]$ |

Across the five pieces there are nine distinct oriented interval triples. Each piece has the port symmetries that preserve its triple: $H_7$ and $H_{15}$ allow swapping their two symmetric branches, while the triangle and $H'_7$ are symmetric in all three ports.

## Induction and finite verification

Record the substitution history of a vertex as a rooted tree: an unexpanded vertex is a leaf, and each internal node consists of the primitive *core* used for its first replacement together with the child pieces substituted at the core's vertices. Because the parent keeps every edge of each child, any forbidden cycle inside a child persists in the parent. If every child is clean, induction reduces each child to one of the nine oriented library choices.

Any simple cycle crossing between children uses two of the at most three boundary edges of each visited child, so it projects to a simple cycle in the core. Conversely, any simple core cycle lifts by choosing a port-to-port path independently inside each visited child, attaining the entire integer interval obtained by summing the endpoints from the table. The checkers [scripts/gadget_csp.py](scripts/gadget_csp.py) and [scripts/recursive_gadgets.py](scripts/recursive_gadgets.py) enumerate all core cycles, search over oriented labelings, and discard any assignment as soon as some core cycle must hit 4, 8, 16, or 32. For every surviving assignment, the code builds the expanded graph explicitly, verifies cleanness by simple-cycle enumeration, and checks isomorphism to a library member by exhaustive search for an adjacency-preserving bijection (in every nontrivial piece, the ports are precisely the degree-two vertices, so any graph isomorphism preserves the port set).

| Three-port core order | Connected simple cores | Clean oriented assignments | Largest clean expansion |
| ---: | ---: | ---: | ---: |
| 3 | 1 | 7 | 15 |
| 5 | 2 | 6 | 15 |
| 7 | 10 | 5 | 15 |
| 9 | 63 | 4 | 15 |
| 11 | 482 | 4 | 15 |
| 13 | 4,541 | 2 | 15 |

Counts are per representative core, with incidences ordered by increasing neighbor index and the free half-edge listed last at each degree-two vertex. This proves closure under the induction step. At the root, the checker tests all 621 connected simple cubic cores of orders 4 through 14 and confirms that every oriented assignment yields a 4-, 8-, 16-, or 32-cycle. To reproduce the table and root check from this directory, put `geng` from [nauty 2.9.3](https://pallini.di.uniroma1.it/) on `PATH` and run `python scripts/recursive_gadgets.py`.

To see that 32 is sharp, orient a Hamiltonian 6-cycle in $K_{3,3}$ and place a copy of $H_{15}$ at each vertex with its distinguished port on the outgoing cycle edge. Every 4-cycle of $K_{3,3}$ misses the outgoing edge of at least one of its vertices (any nonempty vertex set closed under successors contains the entire 6-cycle), so its transit-sum lower endpoint lies between $4 \cdot 4 + 2 = 18$ and $4 \cdot 6 = 24$ while its upper endpoint is 60, capturing 32. Every 6-cycle has lower endpoint at least 24. Together with the internal cleanness of $H_{15}$, this gives a 90-vertex graph whose shortest dyadic cycle has length 32.

## Cubic graphs of treewidth at most three

**Corollary.** Every finite simple cubic graph with neither the 8-vertex Wagner graph $V_8$ nor the pentagonal prism $Q_{10}$ as a minor contains a cycle of length 4, 8, 16, or 32. In particular, this holds for every finite simple cubic graph of treewidth at most three, because $V_8$ and $Q_{10}$ are forbidden minors for treewidth three ([Arnborg, Proskurowski, and Corneil](https://doi.org/10.1016/0012-365X(90)90292-P)).

### Three-edge cuts

Let $H$ be a simple 3-edge-connected cubic graph. Consider a 3-edge cut with at least two vertices on each side. Both shores must be connected, since a disconnected shore would have two components each needing at least three boundary edges. The cut is a matching, because moving a vertex incident to two cut edges to the other side would give a smaller cut. A shore of $r$ vertices has $(3r - 3)/2$ internal edges with $r \ge 3$, so it contains a cycle. Contracting either shore to a single vertex and deleting loops yields a smaller simple 3-edge-connected cubic minor, because every cut in the contracted graph lifts to a cut of the same size in $H$.

Every simple 3-edge-connected cubic graph is also 3-vertex-connected. Deleting one vertex or two adjacent vertices leaves components whose combined edge boundary is at most four, contradicting 3-edge-connectivity. Deleting two nonadjacent vertices $u, v$ leaves at least two components, each needing three boundary edges; both $u$ and $v$ must attach to both components (neither is a cut vertex), so moving $u$ into the component holding two of its neighbors produces a 2-edge cut.

Repeatedly splitting along nontrivial 3-edge cuts stops at cyclically 4-edge-connected cubic graphs. Every such graph on at least 10 vertices has a cyclically 4-edge-connected cubic minor on 10 vertices: any one of order greater than 10 comes from a smaller one by subdividing two nonadjacent edges and joining the new vertices (so the smaller graph is a minor). There are five possibilities at order 10: $Q_{10}$ itself, and four graphs built from $V_8$ by one such edge addition ([Kingan and Kingan, Theorem 2.1, Figure 5, and Section 4](https://www.tandfonline.com/doi/pdf/10.1080/09728600.2024.2333397)). Excluding $V_8$ and $Q_{10}$ therefore forces every terminal graph in the splitting to have order at most 8.

Fix a vertex $z$ of $H$. We can reassemble the split graphs from a terminal cubic core while keeping $z$ unexpanded, by induction on $|V(H)|$. At a split, let $J$ be the minor keeping $z$ and let $y$ be the vertex representing the opposite shore. Build $J$ with $z$ unexpanded, build the opposite minor with its contraction vertex unexpanded, delete that contraction vertex, and insert the resulting three-port piece at $y$. By simplicity and 3-vertex-connectivity, deleting the contraction vertex from its initial core leaves a connected primitive with three distinct degree-two vertices, inside which all later replacements take place. Applying the same reassembly with root cap 14 and primitive cap 13 extends the recursive theorem to every 3-edge-connected simple cubic graph that has no cyclically 4-edge-connected cubic minor on 16 or more vertices.

### Avoiding a specified edge

Take any 3-edge-connected cubic graph $H$ in the $\{V_8, Q_{10}\}$-minor-free class, assign a clean library piece to every vertex, and pick any core edge $e$. We show by induction on $|V(H)|$ that the expanded graph has a 4-, 8-, 16-, or 32-cycle avoiding the edge corresponding to $e$.

* If $H$ has no nontrivial 3-edge cut, then $|V(H)| \le 8$, and $H - e$ is connected with two degree-two vertices and all other vertices cubic. The checker tests all such cores (1 at order 4, 4 at order 6, and 19 at order 8, with the free half-edges representing the removed edge $e$) and finds that every labeling gives a target cycle.
* If a nontrivial 3-edge cut misses $e$, the expanded shore disjoint from $e$ is a recursively built piece (by the marked-vertex reassembly above followed by the given clean vertex substitutions). If it contains a target cycle, we are done. Otherwise, finite closure turns it into a clean library piece up to port permutation. Replace that shore by a vertex with this label in the smaller contraction minor and apply the induction hypothesis to $e$.
* If a nontrivial 3-edge cut contains $e$, both expanded shores are recursively built three-port pieces. If either shore contains a target cycle, we are done. Otherwise both are nontrivial clean library pieces, so each has a transit interval in $\{[2,3], [3,7], [4,7], [4,15], [6,15]\}$ between the other two cut edges. Joining arbitrary port-to-port paths across those two cut edges gives the sum of the two intervals, and checking endpoints directly shows that every pairwise sum in this set contains 4, 8, or 16, giving a target cycle avoiding $e$.

### Cuts of size one or two

Now let $G$ be a connected cubic $\{V_8, Q_{10}\}$-minor-free graph of edge-connectivity at most two. If $G$ has bridges, delete them and take a leaf component $B$ (bridgeless, with one edge to the rest of $G$); otherwise set $B = G$. Inside $B$, pick a nonempty vertex set $A$ of minimum order whose edge boundary in $G$ has size 1 or 2 (the whole leaf component is eligible when $G$ has bridges, and a 2-edge cut gives an eligible set when $B = G$). By minimality, $G[A]$ is connected.

If the boundary of $A$ has size two, its endpoints $x, y \in A$ are distinct and nonadjacent: a shared endpoint could be dropped from $A$ to make a smaller eligible set, and adjacent endpoints could both be dropped (leaving a nonempty set because $G$ is simple and cubic). Both cut edges lie inside $B$ (any proper subset of a bridgeless $B$ has at least two boundary edges inside $B$, while $B$ itself has only one edge leaving it). Also $B - A$ is connected, since each component would need at least two boundary edges in $B$. There is therefore an $x$-$y$ path outside $A$. Adding the edge $e = xy$ to $G[A]$ produces a graph $H$ that is a minor of $G$ (obtained by contracting the exterior path to $e$).

If the boundary of $A$ has size one, let $r \in A$ be incident to the cut edge and let $p, q$ be its two neighbors in $A$. Then $p$ and $q$ are nonadjacent, because otherwise removing $\{r, p, q\}$ from $A$ would leave a smaller nonempty set of boundary size two. Suppressing $r$ gives a simple cubic minor $H$ with new edge $e = pq$.

In either case $H$ is 3-edge-connected: if $H$ had a cut of size at most two, pick a shore avoiding both endpoints of $e$ when they lie on the same side (or either shore when separated); it would be a proper subset of $A$ with the same boundary size in $G$, contradicting minimality. Since $H$ is a minor of $G$, it still excludes $V_8$ and $Q_{10}$. The marked-edge result (with unchanged vertices) gives a target cycle in $H - e \subseteq G[A]$, proving the corollary.

The 90-vertex example above also shows that 32 is sharp in the $\{V_8, Q_{10}\}$-minor-free class. Every minor model of a cubic graph can be reduced to a subdivision by connecting the at most three attachments in each branch set with a tree and suppressing degree-two vertices. Suppose a graph obtained by replacing a vertex with a triangle contains a subdivision of $V_8$ or $Q_{10}$. The triangle holds at most three branch vertices, with at least two outside. If it held two or more, its three boundary edges would separate two sets of at least two branch vertices, contradicting cyclic 4-edge-connectivity of $V_8$ and $Q_{10}$. If it holds one branch vertex, the three edge paths leaving it use distinct boundary edges; if it holds none, at most one path segment passes through the triangle (each passage uses two boundary edges). In both cases, contracting the triangle preserves the subdivision after suppressing extra degree-two vertices. Because the 90-vertex graph is built from $K_{3,3}$ solely by triangle replacements, any $V_8$ or $Q_{10}$ minor would already appear in $K_{3,3}$, which has too few vertices.

## An unrestricted-base criterion

Take any connected bridgeless cubic core, and let $c_0, c_T, c_7, c'_7, c_{15}$ count the vertices assigned to each of the five library pieces. The expanded graph contains a dyadic cycle whenever

$$
c_7 + 3c'_7 + 17c_{15} \ge 3(c_0 + c_T).
$$

To prove this, assign weight $b - 2a$ to each transit interval $[a, b]$, and pick a uniform random element of the binary cycle space of the core (the set of edge subsets with even degree at every vertex). At any vertex, the chosen edges form either the empty set or a pair of edges. Restricting the cycle space to its three incident edges gives a linear subspace of the two-dimensional even-parity subspace of $\mathbb{F}_2^3$. Since the core is bridgeless, every edge lies in some cycle; any proper subspace would force one coordinate to be identically zero, so the restriction is surjective and each of the four local states occurs with probability $1/4$.

Across the five rows of the interval table, the three transit weights at a vertex sum to $-3, -3, 1, 3, 17$. The inequality above makes the expected total weight nonnegative. Every nonempty even subgraph of a cubic graph decomposes into vertex-disjoint simple cycles, and at least one nonempty even subgraph exists. If every simple cycle had negative weight, the expectation would be strictly negative. Some simple cycle therefore has total weight $B - 2A \ge 0$, where $[A, B]$ is its transit interval. Since $A \ge 3$, this interval contains a power of two at least four.

In particular, every expansion of an arbitrary connected simple cubic core using only $H_7, H'_7, H_{15}$ has a dyadic cycle, even when the core has bridges. Delete all bridges and pick a leaf component of the resulting component tree. Its single attachment vertex has degree two in the leaf, while all other vertices have degree three and every internal edge lies on a cycle. The degree-two vertex contributes at least $-1/2$ in expectation (its unique pair is used with probability $1/2$), while each of the at least two degree-three vertices contributes at least $1/4$. The total expectation is nonnegative, so the same argument applies.
