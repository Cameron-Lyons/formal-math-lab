# Doubling cycles on an independent set

Call a simple cycle of length $4, 8, 16, \ldots$ a *dyadic cycle*, and call a nonempty finite simple graph of minimum degree at least three with no dyadic cycle a *counterexample*.

**Suppression lemma.** Let $A, B$ be the shores of a bipartite subgraph of a graph $G$ with no dyadic cycle. Suppose every used vertex $b \in B$ has degree exactly two in the subgraph, with neighbors $x, y \in A$. Replace each path $xby$ by the edge $xy$ to form a graph $J$ on $A$. Then $J$ keeps the subgraph's degrees on $A$. It is simple because two paths producing the same edge would form a 4-cycle in $G$. Every cycle in $J$ lifts to a simple cycle of twice its length in $G$ when we reinsert the distinct vertices $b$, so $J$ has no dyadic cycle either. The degree and cycle-lifting steps are formalized in [Erdos64/EvenNeighborhood.lean](Erdos64/EvenNeighborhood.lean).

In a minimum-order counterexample, every nonempty independent set $X$ must have some outside vertex with 1 or at least 3 neighbors in $X$. Otherwise, keeping only edges incident to $X$ and suppressing outside vertices would give a smaller counterexample on $X$ with the same degrees (proved in [Erdos64/EvenNeighborhood.lean](Erdos64/EvenNeighborhood.lean)). In particular, if every outside vertex has at most three neighbors in an independent set $A$, the adjacency columns of $A$ on the outside vertices are linearly independent over $\mathbf{F}_2$: a nonzero linear dependence would pick out a nonempty $X \subseteq A$ meeting every outside neighborhood in 0 or 2 vertices.

## A smallest cubic counterexample is nonbipartite

Suppose a cubic bipartite counterexample has shores $A, B$ of size $m$. For each subset of $A$, record the parity of its neighbor count at every vertex of $B$ except one fixed vertex $b$. Because there are $2^m$ subsets and only $2^{m-1}$ records, two subsets share the same record. Their symmetric difference $X$ is nonempty and meets every neighborhood outside $b$ in 0 or 2 vertices. Since $A$ itself meets every neighborhood in 3 vertices, $X$ is a proper subset of $A$.

If $b$ also has an even number of neighbors in $X$, suppressing $B$ gives a smaller cubic counterexample on $X$. Otherwise, delete one edge from $b$ to $X$ before suppressing. Exactly one vertex $x \in X$ drops to degree two. Take two disjoint copies of the component of $x$ and join the two copies of $x$ by a bridge. The new graph is cubic, every cycle stays inside one copy, and it has at most $2|X| < 2m$ vertices.

## Counting odd rows

Let $A$ be a nonempty independent set in a cubic graph with no dyadic cycle, let $B$ be its complement, and let $M$ be the binary adjacency matrix with rows indexed by $B$ and columns by $A$. For a subset $X \subseteq A$ with indicator vector $z$, the ones in $Mz$ mark the vertices of $B$ that have an odd number of neighbors in $X$. Delete one selected edge at each odd row and suppress the remaining vertices of $B$. Each of the $|B|$ rows keeps at most two edges, so

$$3|X| - |Mz| \le 2|B|,$$

where $|Mz|$ is Hamming weight.

For any nonempty $X$, this gives lower bounds on $|X|$ in terms of $c, p, q$, where $c, p, q$ are positive integer lower bounds on the order of a connected dyadic-cycle-free graph whose vertices are cubic except for 0, 1, or 2 degree-two vertices. The known values are $c = 50$ ([Ducoffe and Dumitru, Theorem 5.1](https://arxiv.org/html/2609.28594v1#S5)), $p = 41$, and $q = 32$ ([Bridges.md](Bridges.md)).

| Odd rows | Degrees lost on $X$ | Lower bound on the size of $X$ |
| ---: | --- | ---: |
| 0 | None | $c$ |
| 1 | One vertex drops to degree two | $p$ |
| 2 | Two vertices each lose one, or one vertex loses two | $\min(q, p + 1)$ |

To verify the last row: if two distinct vertices lose one degree each, either they lie in the same component (order at least $q$) or they lie in separate components (combined order at least $2p \ge p + 1$). If both deleted edges hit the same vertex, removing that degree-one leaf leaves a one-terminal component of order at least $p$.

When $M$ is square and invertible, taking $z = M^{-1}e_b$ for any coordinate vector $e_b$ gives one odd row, so $2m \ge 3p - 1 = 122$. Counting distances between pairs of inverse columns improves this to **136** (see [BipartiteBounds.md](BipartiteBounds.md)).

## A cut inequality for arbitrary vertex sets

Let $G$ be a minimum-order counterexample on $n$ vertices, take any nonempty proper subset $A \subsetneq V(G)$, and set $B = \{b \notin A : |N(b) \cap A| \ge 2\}$. Then some nonempty $T \subseteq A$ satisfies

$$
3|T| - \sum_{b \in B} \min(2, |N(b) \cap T|) \ge \begin{cases}
2, & 2|A| < n, \\
1, & 2|A| \ge n.
\end{cases}
$$

To prove this, build a flow network from a source through $A$ and $B$ to a sink, with capacities 3 from the source to $A$, 1 on edges between $A$ and $B$, and 2 from $B$ to the sink. For any cut whose source-side vertices in $A$ form a set $T$, each vertex $b \in B$ can sit on whichever side of the cut contributes less. The minimum cut with that $T$ therefore has capacity $3(|A| - |T|) + \sum_{b \in B} \min(2, |N(b) \cap T|)$, so the largest deficit above equals $3|A|$ minus the maximum integral flow.

If this maximum deficit were zero, we could take the edges used by a full flow, add one extra neighbor in $A$ to every singly used $b \in B$, and suppress $B$ to get a smaller counterexample on $A$. If the deficit were one, at most one vertex of $A$ drops to degree two; when $2|A| < n$, the two-copy bridge repair above again yields a smaller counterexample. Since $T = \emptyset$ has deficit zero, any set achieving the required lower bound is nonempty.

For example, consider a nonempty bipartite graph whose one shore is cubic and whose opposite shore $A$ has minimum degree five. For every $T \subseteq A$, each cubic vertex $b$ satisfies $\min(2, |N(b) \cap T|) \ge \tfrac{2}{3}|N(b) \cap T|$. Summing over $b$ gives at least $\tfrac{10}{3}|T| \ge 3|T|$, so the maximum deficit is zero. Full flow and suppression then produce a smaller unrestricted counterexample on $A$ whenever the original graph has no dyadic cycle.
