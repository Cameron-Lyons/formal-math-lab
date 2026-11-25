# Doubling cycles on an independent set

A dyadic cycle is a simple cycle of length $4,8,16,\ldots$. A counterexample is a nonempty finite simple graph of minimum degree at least three with no dyadic cycle.

**Suppression lemma.** Let $A,B$ be the shores of a bipartite subgraph of a graph $G$ with no dyadic cycle. Suppose each used vertex $b\in B$ has exactly two neighbors, $x,y\in A$. Replace the path $xby$ by the edge $xy$. The graph $J$ on $A$ has the same degrees on $A$ as the subgraph. It is simple because two paths giving the same edge would form a 4-cycle. Each cycle in $J$ lifts to a simple cycle of twice its length in $G$ by reinserting the distinct vertices $b$. Thus $J$ has no dyadic cycle. [Lean degree and cycle-lifting proofs](Erdos64/EvenNeighborhood.lean)

In a minimum-order counterexample, every nonempty independent set $X$ has an outside vertex with exactly one or at least three neighbors in $X$. Otherwise keep the edges incident to $X$. Suppression gives a smaller counterexample on $X$ with all its original degrees. In particular, if each outside vertex has at most three neighbors in an independent set $A$, the adjacency columns of $A$ on the outside vertices are linearly independent over $\mathbf F_2$. A nonzero dependence would select an $X$ meeting every outside neighborhood in zero or two vertices. [Lean minimality proof](Erdos64/EvenNeighborhood.lean)

## A smallest cubic counterexample is nonbipartite

Suppose a cubic bipartite counterexample has shores $A,B$ of size $m$. For each subset of $A$, record the parity of its neighbor count at every vertex of $B$ except one vertex $b$. There are $2^m$ subsets and only $2^{m-1}$ records. Two subsets have the same record. Their symmetric difference $X$ is nonempty and meets every neighborhood except possibly that of $b$ in zero or two vertices. Since $A$ meets each neighborhood in three vertices, $X$ is a proper subset of $A$.

If $b$ also has an even number of neighbors in $X$, suppression gives a smaller cubic counterexample on $X$. Otherwise delete one edge from $b$ to $X$, then suppress. Exactly one vertex $x$ loses one degree. Take two copies of its component and join the copies of $x$ by a bridge. The result is cubic, and every cycle lies in one copy. It has at most $2|X|<2m$ vertices.

## Counting odd rows

For any nonempty independent set $A$ in a cubic graph with no dyadic cycle, let $M$ record adjacency from $A$ to its complement $B$. For a selected set $X\subseteq A$ with indicator vector $z$, the ones in $Mz$ are exactly the vertices of $B$ with an odd number of neighbors in $X$. Drop one selected edge at each such vertex and suppress. Each of the $|B|$ rows keeps at most two edges, so

$$3|X|-|Mz|\le2|B|,$$
where $|Mz|$ denotes Hamming weight.

For nonempty $X$ the following lower bounds result. Here $c,p,q$ are positive integer lower bounds on the order of a connected graph with no dyadic cycle, all of whose vertices are cubic except for respectively zero, one or two degree-two vertices. The available bounds are $c=50$, $p=41$ and $q=32$. [Cubic bound, Theorem 5.1](https://arxiv.org/html/2609.28594v1#S5) · [One- and two-terminal bounds](Bridges.md)

| Odd rows | Degrees lost on $X$ | Lower bound on the size of $X$ |
|---:|---|---:|
| 0 | None | $c$ |
| 1 | One vertex becomes degree two | $p$ |
| 2 | Two vertices each lose one, or one vertex loses two | $\min(q,p+1)$ |

For two distinct deficient vertices, their common component has order at least $q$, or their separate components together have order at least $2p\ge p+1$. When both deletions hit one vertex, removing that leaf leaves a one-terminal component of order at least $p$. These three cases give the last row.

For example, when $M$ is square and invertible, take $z=M^{-1}e_b$ for any coordinate vector $e_b$. The one-odd-row bound gives $2m\ge3p-1=122$. Counting pairs of inverse columns gives **136**. [Bipartite and near-bipartite order bounds](BipartiteBounds.md)

## A cut inequality for arbitrary vertex sets

In a minimum-order counterexample $G$ on $n$ vertices, take any nonempty proper vertex set $A$. Put $B=\{b\notin A:|N(b)\cap A|\ge2\}$. Some nonempty $T\subseteq A$ satisfies

$$
3|T|-\sum_{b\in B}\min(2,|N(b)\cap T|)\ \ge\begin{cases}
2,&2|A|<n,\\
1,&2|A|\ge n.
\end{cases}
$$

Use a flow network from the source through $A$ and $B$ to the sink, with capacities $3,1,2$ on successive layers. For a cut with source-side branch vertices $T$, each $b$ can be placed on whichever side contributes less. The minimum cut with that $T$ has capacity $3(|A|-|T|)+\sum_b\min(2,|N(b)\cap T|)$. Thus the largest displayed deficit is $3|A|$ minus the maximum integral flow.

If the deficit were zero, use the selected edges and give each singly used $b$ a second neighbor in $A$. Suppression would give a smaller counterexample on $A$. A deficit of one leaves at most one degree-two vertex. If $2|A|<n$, the two-copy bridge construction above again gives a smaller counterexample. The empty set has deficit zero, so a set witnessing the required bound is nonempty.

For example, let one shore of a nonempty bipartite graph be cubic and let the opposite shore $A$ have minimum degree five. For each $T\subseteq A$ every cubic vertex $b$ satisfies $\min(2,|N(b)\cap T|)\ge \tfrac23|N(b)\cap T|$. Summing gives at least $\tfrac{10}3|T|$, so the maximum deficit is zero. Full flow and suppression therefore give a smaller unrestricted counterexample on $A$ whenever the original graph has no dyadic cycle.
