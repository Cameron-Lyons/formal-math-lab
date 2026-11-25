# Separators in an unrestricted counterexample

All graphs are finite and simple. A dyadic cycle has length $4,8,16,\ldots$. In a graph of minimum degree two, call its degree-two vertices *terminals*.

## Putting adjacent disjoint triangles in one block

In searching for a smallest counterexample we can assume that any two disjoint triangles joined by an edge lie in a common 2-connected block. This reduction works at every order.

Choose a counterexample $G$ with fewest vertices, then fewest edges. It is connected. Each edge has a cubic endpoint, since an edge joining higher-degree vertices could be deleted. There is no bridge, since contracting a bridge preserves minimum degree at least three and all cycles.

If $G$ has a cut vertex, choose an end block $B$ minimizing its order, then its number of edges. Let $c$ be its unique cut vertex of $G$. Every other vertex of $B$ keeps its degree. Since $B$ is 2-connected, $c$ has at least two neighbors in $B$. A third would make $B$ a smaller counterexample. Glue two copies of $B$ at $c$. Two distinct end blocks of $G$ share at most one vertex, so the new graph has $2|B|-1\le |G|$ vertices. If equality holds, another end block has the same order and at least as many edges as $B$, so the new graph also has at most as many edges as $G$. It has minimum degree three and all its cycles stay within one copy. Every edge still has a cubic endpoint, since only $c$ can change degree and it had degree at least four in $G$.

A pair of disjoint triangles in different copies can be joined by an edge only if one triangle contains $c$ and the other contains a neighbor of $c$. But if $c$ lies on a triangle in one copy, it does in both. Its two neighbors in each copy already belong to that copy's triangle through $c$. Each neighbor is cubic and belongs to at most one triangle, since two triangles through a cubic vertex would share an edge and form a 4-cycle. Thus every joined pair lies in a common block. The same conclusion holds immediately when $G$ is 2-connected. [Order-41 application](Order41.md)

## A separate test for small vertex cuts

**Lemma.** Every nonempty graph of minimum degree at least two with at most two terminals contains a subgraph of minimum degree at least two with exactly two terminals.

Choose a nonempty subgraph satisfying the hypotheses with the fewest edges. If it has no terminals, delete any edge. If it has exactly one terminal, delete that vertex. In either case the remaining graph is nonempty, still has minimum degree at least two, and has at most two terminals. This contradicts minimality. $\square$

Now let $S$ be a vertex cut of size $s\le2$ in a connected graph $G$ of minimum degree at least three. Choose a smallest component $C$ of $G-S$. In the side $H=G[C\cup S]$ only vertices of $S$ can have degree below three. The side contains a cycle, since a tree with a vertex of degree at least three has at least three leaves. Peel off isolated vertices and leaves. This preserves the cycle and never increases the number of vertices of degree below three. The lemma applies to the remaining graph.

If $|G|\le41$, then $|H|\le\lfloor(41+s)/2\rfloor\le21$. A single exhaustive check finds a 4-, 8- or 16-cycle in every graph on at most 21 vertices with exactly two terminals and minimum degree two. It visits 3,994,439 partial graphs. Thus any connected counterexample through order 41 would be 3-connected. [Checker](scripts/terminal_blocks.cpp)

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

The same checker with wider caps gives the two inputs below. The lemma extends the second row to graphs with at most two terminals. For the first row, the zero-terminal case already follows from the [order-41 theorem](Order41.md). An independent run of `zero-any 28` also covers that case in 22,888,014 states.

| Terminals | Order through which a dyadic cycle is forced | Partial graphs visited | Checker arguments |
| ---: | ---: | ---: | --- |
| Exactly one | 28 | 25,973,958 | `one-any 28` |
| Exactly two | 24 | 36,322,893 | `two-any 24` |

Each side $C\cup S$ contains a nonempty core with at most $s$ terminals by the peeling argument. For a cut vertex, two sides have at least 29 vertices each and share just the cut vertex, giving $29+29-1=57$. For a separating pair, they have at least 25 each and share two vertices, giving $25+25-2=48$. Deleting a bridge gives two disjoint sides of minimum degree at least two with at most one terminal each, giving $29+29=58$.

When $S=\{x,y\}$ is an adjacent pair, the bound improves to 52. We may assume $G$ has no cut vertex since otherwise the bound 57 applies. Every component $C$ of $G-S$ attaches to both $x$ and $y$. In the side $H=G[C\cup S]$ both have degree at least two. If either has degree at least three then $|H|\ge29$. Otherwise each has exactly one neighbor in $C$. These two neighbors are distinct. A common neighbor would be a cut vertex separating the rest of $C$, while a singleton $C$ would violate minimum degree three. Consequently $G[C]$ has minimum degree at least two with at most two terminals. Thus $|C|\ge25$ in either case and two components give $|G|\ge52$.

### How the finite check works

First delete edges between vertices of degree at least four until there is no such edge. This preserves the terminals and minimum degree and can only remove cycles. Expose the two terminals first, trying them adjacent and nonadjacent. For a single terminal start with it and its two neighbors, again trying the optional edge. At each step an exposed vertex below its required degree needs a fresh neighbor. Try every possible set of exposed neighbors of this fresh vertex. Reject a branch if a terminal exceeds degree two, two adjacent vertices exceed degree three, or two of the new neighbors were already joined by a simple path of length $2^k-2$. In the last case the fresh vertex closes a dyadic cycle.

For pruning, any group of exposed vertices that cannot share a fresh neighbor needs as many fresh vertices as the sum of its missing degrees. If that exceeds the remaining slots, discard the branch. Once all degree requirements hold, the exposed graph itself is a candidate, even if disconnected. Following any hypothetical example would reach such a branch. The runs above found none. [Checker source](scripts/terminal_blocks.cpp)

## A reduction to a 3-connected graph with one prescribed edge

**Proposition.** Every connected counterexample contains a subdivision of a 3-vertex-connected simple graph $K$ of treewidth at least four with a distinguished edge $xy$. Every edge other than $xy$ is represented by a single edge. The graph $K-xy$ occurs as a subgraph, has at least 25 vertices, and has no dyadic cycle.

Take a 2-connected end block $B$ of the counterexample, taking the whole graph if it is 2-connected. An end block consisting of a bridge alone would have a non-cut endpoint of degree one. Choose an edge $r_1r_2$ of $B$ incident to its cut vertex if it has one. Every other vertex of $B$ keeps all its neighbors in $B$.

Choose an inclusion-minimal nonempty set $U\subseteq V(B)\setminus\{r_1,r_2\}$ having at most two external neighbors in $B$. The entire complement of the root edge is eligible. The graph on $U$ is connected, since a component of a disconnected choice would be smaller and eligible. Its neighborhood $S$ has exactly two vertices by 2-connectivity. Deleting fewer would leave a root vertex outside $U$ separated from $U$. Write $S=\{x,y\}$, and form $K=B[U\cup S]+xy$ by adding the edge if necessary. Since every vertex of $U$ keeps all its neighbors, $K$ has at least four vertices.

If removing at most two vertices $T$ disconnected $K$, some component $W$ would miss the surviving boundary $S\setminus T$, whose vertices form a clique. Then $W\subseteq U$ and $N_B(W)\subseteq T$. Moreover $W\ne U$, since in that case any surviving boundary vertex has a neighbor in $U$, and with no surviving boundary there is no second component. This contradicts the choice of $U$. Thus $K$ is 3-connected.

If $xy$ was added, some vertex of $B$ lies outside $U\cup S$. Otherwise the two excluded roots would be exactly $x,y$, an adjacent pair. Each component outside $U\cup S$ attaches to both $x$ and $y$ by 2-connectivity of $B$, supplying an exterior path to realize the added edge. All other edges of $K$ are already present. Finally, $K-xy$ has minimum degree at least two, with only $x,y$ possibly of degree two. The finite bound gives $|K|\ge25$. If either endpoint has degree at least four in $K$, the one-terminal bound gives $|K|\ge29$.

In treewidth at most three, a graph of minimum degree at least three has a 4-, 8- or 16-cycle avoiding any prescribed edge. Applied to $K$ and $xy$, this proves the asserted lower bound on treewidth. More generally, for **every** two-vertex separator $\{a,b\}$ of a connected counterexample and **every** component $C$ behind it, the graph on $C\cup\{a,b\}$ after inserting $ab$ has treewidth at least four. Otherwise the graph on that side before inserting the edge would satisfy the two-exception theorem. Its only possible degree defects are $a,b$, which lie together in a bag of a width-three completion. For a three-vertex separator $S$, if the side on $C\cup S$ has treewidth at most three after completing $S$ to a triangle, then $|C|\le15$ and every vertex of $C$ is cubic in $G$. Each member of $S$ has degree at most two in the original side. These statements follow by rooting at $S$ in the verified three-boundary classification. [Treewidth proof and finite certificate](TreewidthThree.md)

It would therefore suffice for the unrestricted conjecture to prove that every finite 3-connected graph has a dyadic cycle avoiding any prescribed edge. There is also an exact equivalence that retains information from both sides.

**Path-length formulation.** Write $L(J;x,y)$ for the lengths of simple $x$–$y$ paths in $J$. Take any finite 3-connected simple graph $K$ with edge $xy$, and any connected finite simple graph $F$ with distinct vertices $x,y$ of degree at least one and all other vertices of degree at least three. Identify only the equally named vertices. Suppose neither $K-xy$ nor $F$ contains a dyadic cycle. The Erdős–Gyárfás conjecture is equivalent to requiring that some $p\in L(K-xy;x,y)$ and $q\in L(F;x,y)$ satisfy $p+q=2^k$ for an integer $k\ge2$ in every such instance.

Indeed, the union of $K-xy$ and $F$ is simple and has minimum degree at least three. A cycle using edges from both sides splits into one simple $x$–$y$ path on each side, and any two such paths form a simple cycle. This proves the path-length requirement from the conjecture. Conversely, extract $K$ and $U$ from any connected counterexample by the construction above and put $F=G-U$, retaining $xy$ if it existed. Every component of $B-(U\cup\{x,y\})$ attaches to both boundary vertices. If there is no such component, $xy$ is an actual edge. Thus $B-U$ is connected, and the remaining blocks of $G$ are attached to it through the cut vertex outside $U$ if there is one. The terminals have degree at least one in $F$ and all other vertices of $F$ keep their original degrees. The two pieces reunite to form $G$, so the required sum cannot occur.

## Bipartite pieces in a minimum counterexample

In a dyadic-cycle-free bipartite graph with two marked vertices of degree at least two and all others of degree at least three, the ports can be repaired to produce a graph of minimum degree at least three on at most the same number of vertices, still without a dyadic cycle. For ports of the same color add an edge. For opposite colors, identification gives only odd new cycles and is possible directly unless the two ports are adjacent and both have degree two. In that case delete both ports and identify their other neighbors. These neighbors are distinct and nonadjacent, by bipartiteness and the absence of a 4-cycle. Lean checks the constructions, degree bounds and cycle transfers. In particular, if deleting a vertex of a minimum-order counterexample leaves a bipartite graph, the deleted vertex had at least three neighbors of degree exactly three. [Lean proof](Erdos64/CutVertex.lean)

Consequently every side $G[C\cup S]$ of every separator of size one or two in a minimum-order counterexample contains an odd cycle. If a side were bipartite, peel it as above. The surviving bipartite core has at most two terminals, and any extra marked vertices needed for the repair can be taken among the vertices of degree at least three. The resulting counterexample has order at most that of the proper side, contradicting minimality.
