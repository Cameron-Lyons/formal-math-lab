# Power-of-two cycles under recursive vertex replacement

**Theorem.** Start with any connected simple cubic graph on at most 14 vertices. Replace any vertex by any connected simple graph on at most 13 vertices having three distinct vertices of degree two and every other vertex cubic. Join the three incident edges of the old vertex to the three degree-two vertices by an arbitrary bijection. Repeat any finite number of times, including at vertices created by previous replacements. Every resulting graph has a simple cycle of length **4, 8, 16, or 32**. The bound 32 is sharp.

This family has unbounded order. The conclusion follows by induction from a finite computation. The computation uses nauty and Python.

## The five possible pieces

A piece has three boundary half-edges. The unchanged vertex carries all three half-edges. Every other primitive piece has one half-edge at each of its three degree-two vertices. When a vertex of a piece is replaced, its boundary half-edges participate in the bijection in the same way as internal edges. Call a piece *clean* when it has no cycle of length 4, 8, 16, or 32.

Up to a permutation of the boundary half-edges, the only clean pieces this recursion can produce are the unchanged vertex, the triangle, $H_7$, $H'_7$, and $H_{15}$. The last three are the seven- and fifteen-vertex pieces in Garcia's library. $H'_7$ can be constructed by subdividing the three edges incident to a single vertex of $K_4$ once each. $H_7$ can be constructed by expanding two vertices of a triangle into triangles. $H_{15}$ can be constructed by putting two copies of $H_7$ at two vertices of a triangle, with the distinguished ports of both copies facing outward. These descriptions also show that all five pieces occur under the order-13 restriction. [Garcia, Sections 3 and 6](https://arxiv.org/html/2609.04686v1#S3)

For each pair of ports, record all possible lengths of a simple path joining them, plus one for a departing edge. Each of these five pieces gives an integer interval. The three columns correspond to the three choices of omitted port, up to permutation.

| Piece | First | Second | Third |
| --- | --- | --- | --- |
| Vertex | $[1,1]$ | $[1,1]$ | $[1,1]$ |
| Triangle | $[2,3]$ | $[2,3]$ | $[2,3]$ |
| $H_7$ | $[4,7]$ | $[3,7]$ | $[3,7]$ |
| $H'_7$ | $[3,7]$ | $[3,7]$ | $[3,7]$ |
| $H_{15}$ | $[6,15]$ | $[4,15]$ | $[4,15]$ |

These five pieces have nine distinct oriented interval triples. Each piece admits the boundary permutations that preserve its triple. For $H_7$ and $H_{15}$ the two identical branches can be swapped, and for the triangle and $H'_7$ all three ports are symmetric.

## Induction and finite verification

Represent the history of a substituted vertex by a rooted tree. An unexpanded vertex is a leaf. At an internal node, the primitive graph used for the first replacement is the core, and the histories at its vertices are the child pieces. Once an internal cycle appears in a completed child, it is also present in the completed parent, because the parent keeps all edges of each child. If every child is clean, induction reduces it to one of the nine oriented choices.

A simple cycle crossing between children uses exactly two of the at most three boundary edges of each visited child. Its projection onto the core is therefore a simple cycle. Conversely, any simple core cycle lifts by choosing one port-to-port path in each of its children independently. Its attainable lengths are the whole integer interval obtained by adding the lower and upper endpoints in the table. The checker enumerates the core cycles, searches the oriented labels, and discards assignments as soon as a core cycle must produce one of the four target lengths. For each surviving assignment it builds the expanded graph explicitly, verifies absence of dyadic cycles by simple-cycle enumeration, and checks isomorphism to a library member by a complete search for an adjacency-preserving bijection. In nontrivial pieces the ports are exactly the degree-two vertices, so a graph isomorphism preserves the set of ports. [Search](scripts/gadget_csp.py) · [Isomorphism and recursion check](scripts/recursive_gadgets.py)

| Three-port core order | Connected simple cores | Clean oriented assignments | Largest clean expansion |
| ---: | ---: | ---: | ---: |
| 3 | 1 | 7 | 15 |
| 5 | 2 | 6 | 15 |
| 7 | 10 | 5 | 15 |
| 9 | 63 | 4 | 15 |
| 11 | 482 | 4 | 15 |
| 13 | 4,541 | 2 | 15 |

Counts are per representative core, with the incidences in increasing neighbor order. The free half-edge at each degree-two vertex comes last. This proves closure under the induction step. At the root the checker tests all 621 connected simple cubic cores of orders 4 through 14. Each oriented assignment at every root produces a 4-, 8-, 16-, or 32-cycle. This completes the induction. To reproduce the table and root check from the package directory, put nauty 2.9.3's `geng` on `PATH` and run `python scripts/recursive_gadgets.py`. [nauty](https://pallini.di.uniroma1.it/)

To attain 32, orient a Hamiltonian six-cycle of $K_{3,3}$. At each vertex attach a copy of $H_{15}$ with its distinguished port on the edge leading to its successor. Any four-cycle omits the outgoing edge of at least one of its vertices, since a nonempty successor-closed vertex set must contain the whole Hamiltonian cycle. Its lower endpoint is between $4\cdot4+2=18$ and $4\cdot6=24$, and its upper endpoint is 60. Every such four-cycle thus lifts to a 32-cycle. Every six-cycle has lower endpoint at least 24. Together with the internal cycle check for $H_{15}$, this gives a 90-vertex graph whose smallest dyadic cycle has length 32.

## Cubic graphs of treewidth at most three

**Corollary.** Every finite simple cubic graph excluding both the eight-vertex Wagner graph $V_8$ and the pentagonal prism $Q_{10}$ as minors contains a cycle of length 4, 8, 16 or 32. In particular, the conclusion holds for every finite simple cubic graph of treewidth at most three, since $V_8$ and $Q_{10}$ are forbidden minors for that class. [Arnborg, Proskurowski and Corneil](https://doi.org/10.1016/0012-365X(90)90292-P)

**Three-edge cuts.** Let $H$ be a simple 3-edge-connected cubic graph. A three-edge cut with at least two vertices on each side has connected shores. Otherwise one shore would contain two components, each with edge boundary at least three. The cut is a matching. If a vertex used two of its edges in the cut, removing it from its shore would give a smaller cut. Each shore with $r$ vertices has $(3r-3)/2$ internal edges and $r\ge3$, so it contains a cycle. Contracting either shore to one vertex and deleting loops gives a smaller simple cubic minor that is still 3-edge-connected. Every cut in the resulting graph lifts to a cut of the same size in $H$.

A simple 3-edge-connected cubic graph is also 3-vertex-connected. For a single deleted vertex or two adjacent deleted vertices, two resulting components would have total boundary at most four, contrary to 3-edge-connectivity. For two nonadjacent vertices $u,v$, two resulting components would each need three boundary edges. Both $u$ and $v$ must attach to both components since neither is a cut vertex. Adding $u$ to the component containing two of its neighbors then gives a cut of size two.

Repeated splitting therefore ends at cubic graphs with no cycle-separating cut of size three. Every such graph on at least ten vertices has a cyclically 4-edge-connected cubic minor on ten vertices. Indeed, a cyclically 4-edge-connected cubic graph of order greater than ten can be obtained from a smaller one by subdividing two nonadjacent edges and joining their subdivision vertices, with each step increasing order by two. The smaller graph is a minor. There are five possibilities at order ten. One is $Q_{10}$ and the other four are obtained from $V_8$ by such an edge addition. Hence in the class under consideration every terminal graph in this splitting has order at most eight. [Kingan and Kingan, Theorem 2.1, Figure 5 and Section 4](https://www.tandfonline.com/doi/pdf/10.1080/09728600.2024.2333397)

For use with boundary edges, fix a vertex $z$ of $H$. The split graphs can be reassembled starting from a terminal cubic core while keeping $z$ as an original, unexpanded vertex. Induct on $|V(H)|$. At a split, let $J$ be the minor retaining $z$ and $y$ the vertex of $J$ representing the opposite shore. Build $J$ with $z$ unexpanded. Build the opposite minor with its contraction vertex unexpanded, delete this contraction vertex, and insert the resulting three-port piece at $y$. Deleting the contraction vertex from its initial core leaves a connected primitive with three distinct degree-two vertices. This follows from 3-vertex-connectivity and simplicity. The later replacements that built the opposite minor can then be performed inside this primitive. The same argument, with root order 14 and primitive order 13, gives the recursive theorem's conclusion for every 3-edge-connected simple cubic graph having no cyclically 4-edge-connected cubic minor on 16 or more vertices.

**Avoiding a specified edge.** For a 3-edge-connected cubic $H$ in the $\{V_8,Q_{10}\}$-minor-free class, assign a clean library piece to every vertex and prescribe any core edge $e$. Its expansion has a target cycle avoiding the edge between the pieces corresponding to $e$. Induct on $|V(H)|$.

* If $H$ has no nontrivial three-edge cut, its order is at most eight. The core $H-e$ is connected with exactly two degree-two vertices and all others cubic. The checker tests all such cores, with one, four and nineteen at orders four, six and eight. No labeling avoids all four target lengths. The free half-edges in this calculation represent the removed $e$.
* If a nontrivial cut misses $e$, consider the expanded shore disjoint from the endpoints of $e$. It is a recursively generated piece by the marked-vertex construction in the previous paragraph, followed by its given clean vertex substitutions. If it contains a target cycle, that cycle avoids $e$. Otherwise the finite closure theorem identifies it with a clean library member, up to a permutation of ports. Replace the entire shore by a vertex labeled with this member in the smaller contraction minor, and apply the induction hypothesis to $e$.
* If the cut contains $e$, each expanded shore is a recursively generated three-port piece. A target cycle in either shore suffices. If both shores are clean, each is a library member. They both have more than one vertex because the cut is nontrivial. The other two cut edges can be joined by arbitrary port-to-port paths inside the two pieces. The resulting cycle lengths form the sum of one transit interval from each piece. These individual intervals belong to $\{[2,3],[3,7],[4,7],[4,15],[6,15]\}$. Every sum of two intervals in this set contains 4, 8 or 16. This can be checked directly from their endpoints. The resulting cycle avoids $e$.

**Cuts of size one or two.** It remains to handle a connected cubic graph $G$ of edge-connectivity at most two, still excluding $V_8$ and $Q_{10}$. If $G$ has bridges, let $B$ be a leaf component after deleting them. This component is bridgeless and has one edge to the rest of $G$. Otherwise take $B=G$. Inside $B$ choose a nonempty set $A$ of smallest possible order whose edge boundary in $G$ has size one or two. A leaf component itself is eligible, and when $B=G$ there is a two-edge cut. The graph induced by $A$ is connected by minimality.

If the boundary has size two, its endpoints $x,y$ in $A$ are distinct and nonadjacent. A repeated endpoint would give a smaller eligible set by removing that vertex. Adjacent endpoints would give one by removing both; some vertices remain because the graph is simple and cubic. Both cut edges lie in $B$. Indeed, a proper subset of a bridgeless $B$ has at least two boundary edges inside $B$, and the entire leaf component has just one edge to the rest of $G$. Also $B-A$ is connected since each of its components would require at least two boundary edges in $B$. There is thus an $x$–$y$ path through the exterior of $A$. Complete $G[A]$ by adding $e=xy$. Contracting this exterior path down to one edge shows that the completion $H$ is a minor of $G$.

If the boundary has size one, let $r$ be the vertex of $A$ incident with it. Let $p,q$ be the two neighbors of $r$ in $A$. The vertices $p,q$ are nonadjacent; otherwise removing $r,p,q$ from $A$ leaves a nonempty smaller set of boundary two, using simplicity and cubicity. Suppress $r$ to obtain a simple cubic minor $H$ with new edge $e=pq$.

In either case $H$ is 3-edge-connected. If there were a cut of size at most two, take a shore that avoids both endpoints of $e$ when they are on the same side, and either shore when they are separated. Its edge boundary in $G$ has the same size as in $H$, by construction, and it is a proper subset of $A$. This contradicts minimality. Since $H$ inherits the two minor exclusions, the marked-edge result, with all its vertices unchanged, gives a target cycle avoiding $e$. The graph $H-e$ is a subgraph of $G[A]$, which proves the corollary.

The 90-vertex example also attains 32 in the two-excluded-minor class. Every minor model of a cubic graph can be chosen as a subdivision, by connecting the at most three attachments in each branch set with a tree and suppressing degree-two vertices. Consider such a subdivision of $V_8$ or $Q_{10}$ in a graph obtained by replacing a vertex with a triangle. The new triangle contains at most three branch vertices, with at least two outside. If it contained two or more, the three boundary edges would separate two sets of at least two branch vertices, inducing a forbidden cut of at most three in the modeled cyclically 4-edge-connected graph. If it contains one branch vertex, the three edge paths from that vertex to its three neighbors use distinct boundary edges. If it contains none, at most one segment of an edge path passes through the triangle, since each passage needs two boundary edges. In both cases contracting the triangle preserves the subdivision after suppression of redundant degree-two vertices. The 90-vertex example comes from $K_{3,3}$ by triangle replacements alone. Either forbidden minor would thus have to occur already in $K_{3,3}$, which is too small.

## An unrestricted-base criterion

For an arbitrary connected bridgeless cubic core, write $c_0,c_T,c_7,c'_7,c_{15}$ for the numbers of vertices assigned each of the five pieces. The expansion contains a dyadic cycle whenever

$$
c_7+3c'_7+17c_{15}\ \ge\ 3(c_0+c_T).
$$

To prove this, give a transit with interval $[a,b]$ weight $b-2a$. Choose uniformly from the binary cycle space of the core, the set of edge subsets of even degree at every vertex. At any vertex the incident edges present form the empty set or a pair. The restriction of the cycle space to its three incident edges is a linear subspace of the even-parity subspace of $\mathbb F_2^3$. Each incident edge belongs to some cycle since the graph is bridgeless. Any proper subspace of that two-dimensional subspace leaves at least one of the three coordinates identically zero. Thus the restriction is surjective and each of the four local states has probability $1/4$.

The three transit weights sum to $-3,-3,1,3,17$ for the five rows above. The displayed inequality makes the expected total weight nonnegative. A nonempty even subgraph of a cubic graph is a disjoint union of simple cycles, and at least one nonempty even subgraph exists. If every simple cycle had negative weight, the expectation would be negative. Some cycle therefore has total weight $B-2A\ge0$, where $[A,B]$ is its interval. Since $A\ge3$, the interval contains a power of two at least four.

In particular, every expansion of an arbitrary connected simple cubic core using only $H_7,H'_7,H_{15}$ has a dyadic cycle, even when the core has bridges. Delete all bridges and choose a leaf of the tree of components. Its single attachment vertex has degree two in the leaf and all other vertices have degree three. All internal edges are on cycles. The degree-two vertex contributes at least $-1/2$ in expectation, since its unique pair is used with probability $1/2$. Each of the other vertices contributes at least $1/4$. The leaf contains at least three vertices, so its expectation is nonnegative and the same argument applies.
