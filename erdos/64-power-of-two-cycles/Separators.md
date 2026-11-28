# Separators in an Unrestricted Counterexample

What if a counterexample to Erdős Problem #64 can be split apart by removing just one vertex (a *cut vertex*), one edge (a *bridge*), or two vertices (a *separating pair*)? Cutting along a small separator breaks the graph into smaller pieces with at most one or two "damaged" boundary vertices of degree two (called *terminals*).

Studying those pieces yields five sharp structural results for unrestricted counterexamples (with no upper bound on maximum degree):

1. **Adjacent triangles in one block:** When searching for a smallest counterexample, we may assume that any two adjacent disjoint triangles lie in the same $2$-connected block (used in [Order41.md](Order41.md)).
2. **3-connectivity through order 41:** Every connected counterexample on at most $41$ vertices is $3$-vertex-connected.
3. **Order lower bounds for small cuts:** Any connected counterexample has at least **48 vertices** if it has a separating pair (**52** if the pair is adjacent), at least **57** if it has a cut vertex, and at least **58** if it has a bridge.
4. **Reduction to a 3-connected core:** Every connected counterexample contains a subdivision of a $3$-connected graph $K$ on at least **25 vertices** of treewidth at least $4$, with at most one edge subdivided — plus an exact path-length reformulation of the full conjecture.
5. **No bipartite sides:** In a minimum-order counterexample, every side of every $1$- or $2$-vertex separator contains an odd cycle (verified in Lean).

Every graph on this page is finite and simple. A *dyadic cycle* is a simple cycle of length $4, 8, 16, \ldots$, and in a graph of minimum degree two, vertices of degree two are called *terminals*.

---

## Putting adjacent disjoint triangles in one block

**The big idea.** If a smallest counterexample $G$ has a cut vertex, pick a smallest $2$-connected *end block* $B$ (a leaf of its block-cut tree) with cut vertex $c$, and mirror $B$ — glue two copies of $B$ together at $c$. The mirrored graph is just as small as $G$, stays a counterexample, and prevents any two triangles on opposite sides of $c$ from being joined by an edge.

When searching for a smallest counterexample, we may therefore assume that **any two vertex-disjoint triangles joined by an edge lie in the same 2-connected block**. This reduction holds at every order.

**Proof.** Choose a counterexample $G$ first with the fewest vertices and then with the fewest edges. Then:
* $G$ is connected.
* Every edge has a cubic endpoint (deleting an edge between two vertices of degree at least four preserves minimum degree three).
* $G$ has no bridge (contracting a bridge preserves minimum degree three and every cycle).

If $G$ is already $2$-connected, the claim holds immediately. Otherwise $G$ has a cut vertex. Pick an end block $B$ minimizing order and then edge count, and let $c$ be its unique cut vertex in $G$. Every other vertex of $B$ keeps its full degree inside $B$. By $2$-connectivity, $c$ has at least two neighbors in $B$; a third neighbor would make $B$ itself a strictly smaller counterexample, so $c$ has degree **exactly two** in $B$.

Now glue two copies of $B$ together at $c$:
* Because any two distinct end blocks of $G$ share at most one vertex, the new graph has $2|B| - 1 \le |G|$ vertices. If equality holds, another end block has the same order and at least as many edges as $B$, so the new graph also has at most as many edges as $G$.
* Every vertex has degree at least three ($c$ now has degree $4$), all cycles stay inside one copy, and every edge still has a cubic endpoint (only $c$ can change degree, and $c$ already had degree at least four in $G$).

Could two disjoint triangles in *different* copies be joined by an edge? The only edges meeting both copies are incident to $c$, so one triangle would have to contain $c$ and the other would have to contain a neighbor of $c$ in the opposite copy. Yet if $c$ lies in a triangle in one copy, it lies in a symmetric triangle in the other copy using both of its neighbors in each copy. Each neighbor of $c$ is cubic (since $c$ has degree $4$ and every edge has a cubic endpoint) and therefore belongs to at most one triangle (two triangles meeting at a cubic vertex would share an edge and form a $4$-cycle). Hence no disjoint triangle can be adjacent across $c$: every edge-joined pair of disjoint triangles lies inside a single block. $\square$

See [Order41.md](Order41.md) for how this cuts the order-$41$ adjacent-triangle search by more than two-thirds.

---

## A separate test for small vertex cuts

To bound the size of a side behind a $1$- or $2$-vertex separator, we first show that any dyadic-cycle-free graph with *at most* two terminals can be trimmed down to one with *exactly* two terminals.

**Lemma.** Every nonempty graph of minimum degree at least two with at most two terminals contains a subgraph of minimum degree at least two with **exactly** two terminals.

**Proof.** Take a nonempty subgraph satisfying the hypotheses with the fewest edges. If it has no terminals, delete any edge; if it has one terminal, delete that vertex. Either step leaves a nonempty subgraph of minimum degree at least two with at most two terminals and strictly fewer edges, contradicting minimality. $\square$

### Peeling a side of a small separator

Now let $S$ be a vertex cut of size $s \le 2$ in a connected graph $G$ of minimum degree at least three, and let $C$ be a smallest component of $G - S$. In the side $H = G[C \cup S]$, only vertices of $S$ can have degree below three. Furthermore, $H$ must contain a cycle, because any tree containing a vertex of degree at least three has at least three leaves (whereas at most $s \le 2$ vertices of $H$ can have degree less than three). Repeatedly deleting isolated vertices and degree-one leaves preserves the cycle and never increases the number of vertices of degree below three, leaving a nonempty *core* of minimum degree at least two with at most $s \le 2$ terminals — to which the Lemma applies.

When $|G| \le 41$, the smallest side satisfies $|H| \le \lfloor (41 + s)/2 \rfloor \le 21$. A single exhaustive run of [scripts/terminal_blocks.cpp](scripts/terminal_blocks.cpp) finds a $4$-, $8$-, or $16$-cycle in every graph on at most $21$ vertices with minimum degree at least two and exactly two terminals, visiting **3,994,439** partial graphs. Every connected counterexample through order $41$ is therefore **3-connected**.

```sh
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror scripts/terminal_blocks.cpp -o /tmp/eg64-terminal-blocks
/tmp/eg64-terminal-blocks two-any 21
```

---

## Larger bounds for individual cuts

Running the same checker with higher order caps produces stronger lower bounds for each type of small cut in a connected counterexample (at arbitrary maximum degree):

| Cut in a connected counterexample | Lower bound on its order |
| --- | ---: |
| Cut vertex | 57 |
| Bridge | 58 |
| Separating pair | 48 |
| Adjacent separating pair | 52 |

These follow directly from two exhaustive exclusions:

| Terminals | Order through which a dyadic cycle is forced | Partial graphs visited | Checker arguments |
| ---: | ---: | ---: | --- |
| Exactly one | 28 | 25,973,958 | `one-any 28` |
| Exactly two | 24 | 36,322,893 | `two-any 24` |

The Lemma above extends the second row to all graphs with *at most* two terminals. For the first row, the zero-terminal case already follows from the [order-41 theorem](Order41.md), and an independent run of `zero-any 28` also confirms it in **22,888,014** states.

### Deriving the four cut bounds

By the peeling argument above, each side $C \cup S$ of a cut of size $s \le 2$ contains a nonempty core of minimum degree at least two with at most $s$ terminals:

* **Cut vertex ($\ge 57$):** Two sides each have at least $29$ vertices and overlap in the single cut vertex, giving $29 + 29 - 1 = 57$.
* **Separating pair ($\ge 48$):** Two sides each have at least $25$ vertices and overlap in the two separator vertices, giving $25 + 25 - 2 = 48$.
* **Bridge ($\ge 58$):** Deleting a bridge leaves two disjoint sides of minimum degree at least two with at most one terminal each, giving $29 + 29 = 58$.
* **Adjacent separating pair ($\ge 52$):** Let $S = \{x, y\}$ be an adjacent separating pair, and assume $G$ has no cut vertex (otherwise the bound $57$ already applies). Then every component $C$ of $G - S$ attaches to both $x$ and $y$, so both $x$ and $y$ have degree at least $2$ in $H = G[C \cup S]$ (one edge from $xy$, plus at least one into $C$).
  * If either $x$ or $y$ has degree at least $3$ in $H$, then $H$ has at most one terminal, so $|H| \ge 29$ and $|C| \ge 27$.
  * Otherwise each of $x$ and $y$ has exactly one neighbor in $C$, and those two neighbors must be distinct: a single common neighbor would be a cut vertex separating the rest of $C$, while $|C| = 1$ would contradict minimum degree three. Thus $G[C]$ itself has minimum degree at least two with at most two terminals, giving $|C| \ge 25$.

  Two components of $G - S$ plus $S$ therefore give $|G| \ge 25 + 25 + 2 = 52$.

### How the finite check works

First delete edges between vertices of degree at least four until none remain; this preserves terminals and minimum degree and can only remove cycles.

1. **Seeds:** For two terminals, expose them first (trying them adjacent and nonadjacent). For one terminal, start with the terminal and its two neighbors (trying the optional edge between those neighbors).
2. **Branching:** At each step, pick an exposed vertex below its required degree, add a fresh neighbor, and try every subset of exposed vertices as its neighborhood. Reject a branch if a terminal exceeds degree two, if two adjacent vertices both exceed degree three, or if two chosen neighbors are already joined by an exposed simple path of length $2^k - 2$ (which would close a dyadic cycle).
3. **Pruning and completion:** Any group of exposed vertices that cannot share a fresh neighbor needs at least as many fresh vertices as the sum of its missing degrees; if that exceeds the remaining vertex slots, prune the branch. Once every exposed vertex meets its degree requirement, the exposed graph is reported as a candidate, even if disconnected. Every hypothetical example would reach such a leaf, and the runs of [scripts/terminal_blocks.cpp](scripts/terminal_blocks.cpp) above found none.

---

## A reduction to a 3-connected graph with one prescribed edge

**The big idea.** Even if a counterexample is full of $1$- and $2$-vertex cuts, zoom into an inclusion-minimal "atomic" cluster $U$ behind a $2$-vertex boundary $\{x, y\}$ inside a $2$-connected end block $B$. Adding the virtual edge $xy$ — realized in $G$ by a path outside $U$ — turns $B[U \cup \{x, y\}]$ into a genuine $3$-connected graph $K$ with no dyadic cycle avoiding $xy$. Our finite bounds and treewidth-three classification immediately force $K$ to be both large ($\ge 25$ vertices) and structurally complex (treewidth $\ge 4$).

**Proposition.** Every connected counterexample contains a subdivision of a $3$-vertex-connected simple graph $K$ of treewidth at least four with a distinguished edge $xy$, in which every edge other than $xy$ is unsubdivided. The graph $K - xy$ occurs as a subgraph, has at least $25$ vertices, and has no dyadic cycle.

**Proof.** Pick a $2$-connected end block $B$ of the counterexample (taking $B = G$ if $G$ is $2$-connected; a bridge cannot be an end block because its non-cut endpoint would have degree $1$). Choose an edge $r_1 r_2$ of $B$ incident to its cut vertex if it has one; every vertex of $B$ other than that cut vertex keeps all its neighbors inside $B$.

Take an inclusion-minimal nonempty set $U \subseteq V(B) \setminus \{r_1, r_2\}$ having at most two external neighbors in $B$ (the entire complement $V(B) \setminus \{r_1, r_2\}$ is eligible):

1. **Connectedness and exact boundary size:** $B[U]$ is connected, because a single component of a disconnected set would be smaller and still eligible. By $2$-connectivity of $B$, the neighborhood $S = N_B(U)$ has size **exactly two** (fewer would separate $U$ from a root vertex outside $U$). Write $S = \{x, y\}$ and set $K = B[U \cup S] + xy$. Because every vertex of $U$ keeps its full degree ($\ge 3$) inside $B[U \cup S]$, we have $|K| \ge 4$.
2. **$K$ is 3-vertex-connected:** Suppose for contradiction that removing a set $T$ of at most two vertices disconnected $K$. Because the surviving boundary $S \setminus T$ is a clique (via the edge $xy$), it sits inside a single component of $K - T$, so some other component $W$ of $K - T$ misses $S \setminus T$. Then $W \subseteq U$ and $N_B(W) \subseteq T$. Moreover $W \ne U$: if $S \setminus T$ is nonempty, every vertex in it has a neighbor in $U$, while if $S \setminus T$ is empty, $K - T = B[U]$ is connected and has no second component. Thus $W$ is a proper nonempty subset of $U$ with $|N_B(W)| \le 2$, contradicting the minimality of $U$.
3. **Realizing $xy$ and bounding $|K|$:** If $xy$ was not already an edge of $B$, then some vertex of $B$ must lie outside $U \cup S$ (otherwise $\{x, y\} = \{r_1, r_2\}$, which is already an edge). By $2$-connectivity of $B$, every component outside $U \cup S$ attaches to both $x$ and $y$, supplying an exterior $x$-$y$ path that realizes $xy$ as a subdivided edge while every other edge of $K$ is already present unsubdivided. Finally, $K - xy$ has minimum degree at least two with at most $x$ and $y$ of degree two, so the finite bound above forces $|K| \ge 25$ (and $|K| \ge 29$ if either $x$ or $y$ has degree at least four in $K$, meaning at least three in $K - xy$).
4. **Treewidth at least four:** By the [treewidth-three theorem](TreewidthThree.md), any graph of treewidth at most three and minimum degree at least three has a $4$-, $8$-, or $16$-cycle avoiding any chosen edge. Applying this to $K$ and $xy$ proves that $K$ has treewidth at least four.

More generally, the treewidth-three theorem constrains *every* small separator of a connected counterexample:
* For **every** $2$-vertex separator $\{a, b\}$ and **every** component $C$ behind it, adding $ab$ to $G[C \cup \{a, b\}]$ produces a graph of treewidth at least four (otherwise $G[C \cup \{a, b\}]$ would satisfy the two-exception theorem in [TreewidthThree.md](TreewidthThree.md), since its only possible degree drops are at $a$ and $b$, which share a bag in a width-three completion).
* For a $3$-vertex separator $S$, if making $S$ a triangle in $G[C \cup S]$ yields treewidth at most three, rooting at $S$ in the verified three-boundary classification forces $|C| \le 15$, makes every vertex of $C$ cubic in $G$, and bounds the degree of every vertex of $S$ inside $G[C \cup S]$ by two. $\square$

Proving that every finite $3$-connected graph has a dyadic cycle avoiding any prescribed edge would therefore settle the full conjecture. There is also an exact equivalence that keeps both sides of the decomposition.

### Path-length formulation

Write $L(J; x, y)$ for the set of edge lengths of simple $x$-$y$ paths in a graph $J$. Let $K$ be any finite $3$-connected simple graph with an edge $xy$, and let $F$ be any connected finite simple graph with distinct vertices $x, y$ of degree at least one and all other vertices of degree at least three. Glue $K - xy$ and $F$ along $x$ and $y$, and suppose neither side contains a dyadic cycle.

**Equivalence.** The Erdős–Gyárfás conjecture is equivalent to requiring that every such pair $(K, F)$ has $p \in L(K - xy; x, y)$ and $q \in L(F; x, y)$ with $p + q = 2^k$ for some integer $k \ge 2$.

* **Forward direction:** The union of $K - xy$ and $F$ is simple and has minimum degree at least three. Any cycle using edges from both sides splits into a simple $x$-$y$ path in $K - xy$ and a simple $x$-$y$ path in $F$, and conversely any two such paths concatenate into a simple cycle. A dyadic cycle in the glued graph therefore gives $p + q = 2^k$.
* **Converse:** Given any connected counterexample $G$, extract $K$ and $U$ as in the Proposition above and set $F = G - U$ (keeping the edge $xy$ in $F$ if it was already an edge of $G$). Every component of $B - (U \cup \{x, y\})$ attaches to both $x$ and $y$, and if no such component exists then $xy$ is already an edge; hence $B - U$ is connected, and any remaining blocks of $G$ attach to it through the cut vertex outside $U$. Both $x$ and $y$ have degree at least one in $F$, all other vertices of $F$ keep their full degrees ($\ge 3$), and gluing $K - xy$ back to $F$ recovers $G$, so no power-of-two sum $p + q$ can exist.

---

## Bipartite pieces in a minimum counterexample

**The big idea.** Inside a bipartite graph, every cycle has even length, and every path between two vertices in the *same* color class has even length while every path between *opposite* color classes has odd length. That parity gives us a free way to repair two degree-two ports so that every newly created cycle has **odd** length — automatically avoiding all powers of two!

Suppose a bipartite graph has no dyadic cycle, two marked vertices (*ports*) of degree at least two, and all other vertices of degree at least three. We can repair the two marked ports to obtain a dyadic-cycle-free graph of minimum degree at least three on at most as many vertices:

* **Same color class:** Add an edge between the two ports. Every cycle using the new edge combines it with an even-length path in the bipartite graph, producing an **odd** cycle.
* **Opposite color classes (not both adjacent degree-two):** Identify (merge) the two ports directly. Every new cycle passes through the merged vertex along an odd-length path between opposite classes, again creating only **odd** cycles.
* **Adjacent degree-two ports in opposite color classes:** Delete both ports and identify their two remaining neighbors $u$ and $v$. Because the two ports lie in opposite color classes, $u$ and $v$ also lie in opposite color classes (hence are distinct) and cannot be adjacent (otherwise the two ports plus $u, v$ would form a $4$-cycle). Merging $u$ and $v$ therefore keeps simplicity, creates only **odd** new cycles, and gives the merged vertex degree at least $(3 - 1) + (3 - 1) = 4$.

Lean verifies these constructions, degree bounds, and cycle transfers in [Erdos64/CutVertex.lean](Erdos64/CutVertex.lean).

### Two consequences for minimum-order counterexamples

1. **Deleting a vertex to get a bipartite graph:** If deleting a single vertex $v$ from a minimum-order counterexample leaves a bipartite graph, then $v$ must have had **at least three neighbors of degree exactly three** (otherwise $G - v$ would be a smaller bipartite graph with at most two degree-two ports, which repairs to a smaller counterexample).
2. **Every side of a 1- or 2-vertex separator is nonbipartite:** In a minimum-order counterexample, every side $G[C \cup S]$ of every $1$- or $2$-vertex separator contains an **odd cycle**. If a side were bipartite, peeling it as above would yield a bipartite core with at most two terminals (picking any extra marked ports among vertices of degree at least three if fewer than two terminals remain). Repairing that core would then produce a counterexample of order at most that of the proper side, contradicting minimality.
