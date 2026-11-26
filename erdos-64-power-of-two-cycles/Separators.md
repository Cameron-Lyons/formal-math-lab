# Separators in an unrestricted counterexample

Every graph on this page is finite and simple. A *dyadic cycle* is a simple cycle of length $4, 8, 16, \ldots$, and in a graph of minimum degree two, vertices of degree two are called *terminals*.

## Putting adjacent disjoint triangles in one block

When searching for a smallest counterexample, we may assume that any two disjoint triangles joined by an edge lie in the same 2-connected block. This reduction holds at every order.

Choose a counterexample $G$ first with the fewest vertices and then with the fewest edges. Then $G$ is connected, every edge has a cubic endpoint (an edge between two higher-degree vertices could be deleted), and $G$ has no bridge (contracting a bridge preserves minimum degree three and every cycle).

If $G$ has a cut vertex, pick an end block $B$ minimizing order and then edge count, and let $c$ be its unique cut vertex in $G$. Every other vertex of $B$ keeps its full degree in $B$. By 2-connectivity, $c$ has at least two neighbors in $B$; a third neighbor would make $B$ a smaller counterexample, so $c$ has degree two in $B$. Glue two copies of $B$ together at $c$. Since two distinct end blocks of $G$ share at most one vertex, the new graph has $2|B| - 1 \le |G|$ vertices. If equality holds, another end block has the same order and at least as many edges as $B$, so the new graph also has at most as many edges as $G$. It has minimum degree three, all of its cycles stay inside one copy, and every edge still has a cubic endpoint (only $c$ can change degree, and $c$ already had degree at least four in $G$).

Two disjoint triangles in different copies can be joined by an edge only if one triangle uses $c$ and the other uses a neighbor of $c$. If $c$ lies in a triangle in one copy, it lies in a symmetric triangle in the other, using both of its neighbors in each copy. Each such neighbor is cubic and therefore belongs to at most one triangle (two triangles meeting at a cubic vertex would share an edge and create a 4-cycle). Hence every edge-joined pair of disjoint triangles lies in one block. If $G$ is already 2-connected, the claim holds immediately. See [Order41.md](Order41.md) for the application to the order-41 search.

## A separate test for small vertex cuts

**Lemma.** Every nonempty graph of minimum degree at least two with at most two terminals contains a subgraph of minimum degree at least two with exactly two terminals.

**Proof.** Take a nonempty subgraph satisfying the hypotheses with the fewest edges. If it has no terminals, delete any edge; if it has one terminal, delete that vertex. Either step leaves a nonempty subgraph of minimum degree at least two with at most two terminals and fewer edges, contradicting minimality. $\square$

Now let $S$ be a vertex cut of size $s \le 2$ in a connected graph $G$ of minimum degree at least three, and let $C$ be a smallest component of $G - S$. In the side $H = G[C \cup S]$, only vertices of $S$ can have degree below three. Also $H$ contains a cycle, since any tree with a vertex of degree at least three has at least three leaves. Repeatedly deleting isolated vertices and leaves preserves the cycle and never increases the number of vertices of degree below three, leaving a core to which the lemma applies.

When $|G| \le 41$, we have $|H| \le \lfloor (41 + s)/2 \rfloor \le 21$. A single exhaustive run of [scripts/terminal_blocks.cpp](scripts/terminal_blocks.cpp) finds a 4-, 8-, or 16-cycle in every graph on at most 21 vertices with minimum degree two and exactly two terminals, visiting 3,994,439 partial graphs. Every connected counterexample through order 41 is therefore 3-connected.

```sh
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror scripts/terminal_blocks.cpp -o /tmp/eg64-terminal-blocks
/tmp/eg64-terminal-blocks two-any 21
```

## Larger bounds for individual cuts

| Cut in a connected counterexample | Lower bound on its order |
| --- | ---: |
| Cut vertex | 57 |
| Bridge | 58 |
| Separating pair | 48 |
| Adjacent separating pair | 52 |

Running the same checker with higher order caps gives the two bounds below. The lemma extends the second row to all graphs with at most two terminals. For the first row, the zero-terminal case already follows from the [order-41 theorem](Order41.md), and an independent run of `zero-any 28` also confirms it in 22,888,014 states.

| Terminals | Order through which a dyadic cycle is forced | Partial graphs visited | Checker arguments |
| ---: | ---: | ---: | --- |
| Exactly one | 28 | 25,973,958 | `one-any 28` |
| Exactly two | 24 | 36,322,893 | `two-any 24` |

By the peeling argument above, each side $C \cup S$ contains a nonempty core with at most $s$ terminals. For a cut vertex, two sides each have at least 29 vertices and share one vertex, giving $29 + 29 - 1 = 57$. For a separating pair, two sides each have at least 25 vertices and share two vertices, giving $25 + 25 - 2 = 48$. Deleting a bridge leaves two disjoint sides of minimum degree at least two with at most one terminal each, giving $29 + 29 = 58$.

When $S = \{x, y\}$ is an adjacent separating pair, the bound rises to 52. Assume $G$ has no cut vertex (otherwise the bound 57 already applies). Every component $C$ of $G - S$ then attaches to both $x$ and $y$, so both have degree at least two in $H = G[C \cup S]$. If either has degree at least three in $H$, then $|H| \ge 29$. Otherwise each has exactly one neighbor in $C$, and those two neighbors are distinct: a single common neighbor would be a cut vertex separating the rest of $C$, while $|C| = 1$ would violate minimum degree three. In that case $G[C]$ has minimum degree at least two with at most two terminals, so $|C| \ge 25$. Two components therefore give $|G| \ge 52$.

### How the finite check works

First delete edges between vertices of degree at least four until none remain; this preserves terminals and minimum degree and can only remove cycles. For two terminals, expose them first (trying them adjacent and nonadjacent). For one terminal, start with the terminal and its two neighbors (again trying the optional edge between those neighbors). At each step, pick an exposed vertex below its required degree, add a fresh neighbor, and try every subset of exposed vertices as its neighborhood. Reject a branch if a terminal exceeds degree two, if two adjacent vertices both exceed degree three, or if two chosen neighbors are already joined by an exposed simple path of length $2^k - 2$ (which would close a dyadic cycle).

For pruning, any group of exposed vertices that cannot share a fresh neighbor needs at least as many fresh vertices as the sum of its missing degrees; if that exceeds the remaining vertex slots, prune the branch. Once every exposed vertex meets its degree requirement, the exposed graph is reported as a candidate, even if disconnected. Every hypothetical example would reach such a leaf, and the runs of [scripts/terminal_blocks.cpp](scripts/terminal_blocks.cpp) above found none.

## A reduction to a 3-connected graph with one prescribed edge

**Proposition.** Every connected counterexample contains a subdivision of a 3-vertex-connected simple graph $K$ of treewidth at least four with a distinguished edge $xy$, in which every edge other than $xy$ is unsubdivided. The graph $K - xy$ occurs as a subgraph, has at least 25 vertices, and has no dyadic cycle.

**Proof.** Pick a 2-connected end block $B$ of the counterexample (taking $B = G$ if $G$ is 2-connected; a bridge cannot be an end block because its non-cut endpoint would have degree one). Choose an edge $r_1 r_2$ of $B$ incident to its cut vertex if it has one; every other vertex of $B$ keeps all its neighbors inside $B$.

Take an inclusion-minimal nonempty set $U \subseteq V(B) \setminus \{r_1, r_2\}$ having at most two external neighbors in $B$ (the entire complement of $\{r_1, r_2\}$ is eligible). Then $B[U]$ is connected, since a component of a disconnected set would be smaller and still eligible. By 2-connectivity, $S = N_B(U)$ has size exactly two (fewer would separate $U$ from a root vertex outside $U$). Write $S = \{x, y\}$ and set $K = B[U \cup S] + xy$. Because every vertex of $U$ keeps its full degree, $|K| \ge 4$.

To see that $K$ is 3-connected, suppose removing a set $T$ of at most two vertices disconnected $K$. Since the surviving boundary $S \setminus T$ is a clique, some component $W$ of $K - T$ misses $S \setminus T$. Then $W \subseteq U$ and $N_B(W) \subseteq T$. Also $W \ne U$: if $S \setminus T$ is nonempty, every vertex in it has a neighbor in $U$, and if $S \setminus T$ is empty, no second component exists. This contradicts the minimality of $U$.

If the edge $xy$ had to be added, some vertex of $B$ lies outside $U \cup S$ (otherwise $\{x, y\}$ would be the adjacent root pair $\{r_1, r_2\}$). By 2-connectivity of $B$, every component outside $U \cup S$ attaches to both $x$ and $y$, giving an exterior path that realizes $xy$, while all other edges of $K$ are already present. Finally, $K - xy$ has minimum degree at least two with at most $x$ and $y$ of degree two, so the finite bound gives $|K| \ge 25$ (and $|K| \ge 29$ if either $x$ or $y$ has degree at least four in $K$).

By the [treewidth-three theorem](TreewidthThree.md), any graph of treewidth at most three and minimum degree at least three has a 4-, 8-, or 16-cycle avoiding any chosen edge. Applying this to $K$ and $xy$ proves that $K$ has treewidth at least four. More generally, for **every** 2-vertex separator $\{a, b\}$ of a connected counterexample and **every** component $C$ behind it, adding $ab$ to $G[C \cup \{a, b\}]$ produces a graph of treewidth at least four (otherwise $G[C \cup \{a, b\}]$ would satisfy the two-exception theorem, since its only possible degree drops are at $a, b$, which share a bag in a width-three completion). Similarly, for a 3-vertex separator $S$, if making $S$ a triangle in $G[C \cup S]$ gives treewidth at most three, rooting at $S$ in the verified three-boundary classification forces $|C| \le 15$, makes every vertex of $C$ cubic in $G$, and bounds the degree of every vertex of $S$ inside $G[C \cup S]$ by two. $\square$

Proving that every finite 3-connected graph has a dyadic cycle avoiding any prescribed edge would therefore settle the full conjecture. There is also an exact equivalence that keeps both sides of the decomposition.

### Path-length formulation

Write $L(J; x, y)$ for the set of edge lengths of simple $x$-$y$ paths in a graph $J$. Let $K$ be any finite 3-connected simple graph with an edge $xy$, and let $F$ be any connected finite simple graph with distinct vertices $x, y$ of degree at least one and all other vertices of degree at least three. Glue $K - xy$ and $F$ along $x$ and $y$, and suppose neither side contains a dyadic cycle. The Erdős-Gyárfás conjecture is equivalent to requiring that every such pair $(K, F)$ has $p \in L(K - xy; x, y)$ and $q \in L(F; x, y)$ with $p + q = 2^k$ for some integer $k \ge 2$.

To see the forward direction, note that the union of $K - xy$ and $F$ is simple and has minimum degree at least three. Any cycle using edges from both sides splits into a simple $x$-$y$ path on each side, and conversely any two such paths form a simple cycle, so a dyadic cycle gives $p + q = 2^k$. For the converse, extract $K$ and $U$ from any connected counterexample $G$ as above and set $F = G - U$ (keeping $xy$ if it was already an edge of $G$). Every component of $B - (U \cup \{x, y\})$ attaches to both $x$ and $y$, and if there is no such component then $xy$ is already an edge; hence $B - U$ is connected, and any remaining blocks of $G$ attach to it through the cut vertex outside $U$. The terminals $x, y$ have degree at least one in $F$, all other vertices of $F$ keep their degrees, and gluing $K - xy$ back to $F$ recovers $G$, so no power-of-two sum $p + q$ can exist.

## Bipartite pieces in a minimum counterexample

Suppose a bipartite graph has no dyadic cycle, two marked vertices of degree at least two, and all other vertices of degree at least three. We can repair the two marked ports to obtain a dyadic-cycle-free graph of minimum degree at least three on at most as many vertices:

* If the two ports are in the same color class, add an edge between them.
* If they are in opposite color classes, identify them directly unless they are adjacent and both have degree two (identification creates only odd new cycles).
* If they are adjacent degree-two vertices in opposite color classes, delete both ports and identify their other neighbors (which are distinct and nonadjacent by bipartiteness and the absence of 4-cycles).

Lean verifies these constructions, degree bounds, and cycle transfers in [Erdos64/CutVertex.lean](Erdos64/CutVertex.lean). In particular, if deleting a vertex $v$ from a minimum-order counterexample leaves a bipartite graph, then $v$ must have had at least three neighbors of degree exactly three.

It follows that in a minimum-order counterexample, every side $G[C \cup S]$ of every 1- or 2-vertex separator contains an odd cycle. If a side were bipartite, peeling it as above would yield a bipartite core with at most two terminals (picking any extra marked vertices among vertices of degree at least three). Repairing that core would then produce a counterexample of order at most that of the proper side, contradicting minimality.
