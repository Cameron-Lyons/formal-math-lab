# Doubling Cycles on an Independent Set

Suppose a graph without power-of-two cycles contains a large *independent set* (a set of vertices with no edges between them). Can we compress the graph onto that independent set without accidentally creating a power-of-two cycle? Yes — whenever the vertices outside the independent set each have degree two into it, replacing each two-edge path through an outside vertex by a single edge *doubles* the length of every cycle when lifted back. Because doubling a power of two gives another power of two, a graph free of power-of-two cycles compresses to a strictly smaller graph with the exact same property.

This single compression trick connects Erdős Problem #64 to linear algebra over $\mathbf{F}_2$ (arithmetic modulo $2$) and network flows. It yields three main consequences:

1. Every smallest cubic counterexample is **nonbipartite**.
2. In any cubic dyadic-cycle-free graph, the parity of neighbor counts across an independent set obeys sharp lower bounds (the foundation for the 136- and 150-vertex bounds in [BipartiteBounds.md](BipartiteBounds.md)).
3. Every proper vertex subset of a minimum-order counterexample satisfies a max-flow/min-cut deficit inequality.

Throughout this document, call a simple cycle of length $4, 8, 16, \ldots$ a *dyadic cycle*, and call a nonempty finite simple graph of minimum degree at least three with no dyadic cycle a *counterexample*.

---

## The suppression lemma

**The big idea.** Inside a bipartite subgraph with parts (*shores*) $A$ and $B$, any vertex $b \in B$ of degree exactly two simply acts as a midpoint on a two-edge path $x - b - y$ between two vertices $x, y \in A$. Deleting $b$ and adding the direct edge $xy$ halves the length of every cycle passing through $B$, while leaving degrees on $A$ untouched.

**Suppression lemma.** Let $A, B$ be the shores of a bipartite subgraph of a graph $G$ with no dyadic cycle. Suppose every used vertex $b \in B$ has degree exactly two in the subgraph, with neighbors $x, y \in A$. Replace each path $xby$ by the edge $xy$ to form a graph $J$ on $A$. Then:

1. **Degree preservation:** Every vertex $a \in A$ has the same degree in $J$ as in the bipartite subgraph.
2. **Simplicity:** $J$ has no loops (since $x \ne y$) and no parallel edges — two distinct vertices $b_1, b_2 \in B$ producing the same edge $xy$ would form the 4-cycle $x b_1 y b_2 x$ in $G$.
3. **No dyadic cycles:** Every simple cycle of length $r$ in $J$ lifts to a simple cycle of length $2r$ in $G$ when we reinsert the distinct vertices $b \in B$ along its edges. Because $2r$ is a power of two whenever $r \ge 4$ is a power of two, $J$ has no dyadic cycle either.

The degree-preservation and cycle-lifting steps are formalized in [Erdos64/EvenNeighborhood.lean](Erdos64/EvenNeighborhood.lean).

### Immediate consequence: no "all-even" independent sets

In a minimum-order counterexample $G$, **every nonempty independent set $X$ must have at least one outside vertex with $1$ or at least $3$ neighbors in $X$**.

Otherwise, every outside vertex has $0$ or $2$ neighbors in $X$. Keeping only the edges incident to $X$ produces a bipartite subgraph whose used outside vertices all have degree exactly two, and suppressing them yields a counterexample on $X$ with the same degrees as in $G$ (at least three) — strictly smaller than $G$, a contradiction (proved in [Erdos64/EvenNeighborhood.lean](Erdos64/EvenNeighborhood.lean)).

In particular, suppose $A$ is an independent set such that every outside vertex has at most three neighbors in $A$ (which holds automatically in any cubic graph). Then the only possible even intersection sizes are $0$ and $2$. Over $\mathbf{F}_2$, the adjacency columns indexed by $A$ on the outside vertices must therefore be **linearly independent**: any nonzero linear dependence would pick out a nonempty subset $X \subseteq A$ meeting every outside neighborhood an even number of times — meaning $0$ or $2$ times.

---

## A smallest cubic counterexample is nonbipartite

**Theorem.** No minimum-order cubic counterexample is bipartite.

**Proof strategy.** In a cubic bipartite graph with shores $A, B$ of equal size $m$, we want a nonempty proper subset $X \subsetneq A$ that meets *almost* every vertex of $B$ in an even number ($0$ or $2$) of neighbors. Ignoring one vertex of $B$ leaves only $m - 1$ parity constraints for $m$ binary choices, so the pigeonhole principle hands us such a subset for free. We then suppress $B$ and repair the at most one degree drop caused by the ignored vertex.

**Proof.** Suppose $G$ is a cubic bipartite counterexample with shores $A$ and $B$, each of size $m$ (so $|G| = 2m$). Fix one vertex $b \in B$. For each of the $2^m$ subsets $Y \subseteq A$, record the parity (even or odd) of $|N(v) \cap Y|$ at every vertex $v \in B \setminus \{b\}$. Because there are only $2^{m-1}$ possible parity records, two distinct subsets $Y_1, Y_2 \subseteq A$ share the same record.

Let $X = Y_1 \triangle Y_2$ be their symmetric difference. Then:
* $X$ is nonempty (since $Y_1 \ne Y_2$).
* Every vertex $v \in B \setminus \{b\}$ has an even number of neighbors in $X$ — hence $0$ or $2$, because $v$ has degree three.
* $X$ is a proper subset of $A$, since $A$ itself meets every vertex of $B$ in $3$ (odd) vertices.

Now examine the ignored vertex $b$:

* **Case 1: $|N(b) \cap X|$ is even ($0$ or $2$).** Suppressing all vertices of $B$ produces a cubic counterexample on $|X| < m < 2m$ vertices, contradicting minimality.
* **Case 2: $|N(b) \cap X|$ is odd ($1$ or $3$).** Delete one edge between $b$ and $X$, leaving $0$ or $2$ edges at $b$, and then suppress $B$. In the resulting dyadic-cycle-free graph on $X$, every vertex still has degree three *except* the single endpoint $x \in X$ of the deleted edge, which drops to degree two. Take two disjoint copies of the connected component of $x$ and join the two copies of $x$ by a single bridge edge. Every vertex now has degree three, no simple cycle can cross the bridge (so no dyadic cycle is created), and the new cubic counterexample has at most $2|X| \le 2(m - 1) < 2m$ vertices — again contradicting minimality. $\square$

---

## Counting odd rows

The same delete-and-suppress idea works even when an independent set does not give a full counterexample: every outside vertex with an odd number of neighbors in $X$ simply costs one deleted edge.

Let $A$ be a nonempty independent set in a cubic graph with no dyadic cycle, let $B$ be its complement, and let $M$ be the binary adjacency matrix over $\mathbf{F}_2$ with rows indexed by $B$ and columns indexed by $A$. For any subset $X \subseteq A$ with binary indicator vector $z \in \mathbf{F}_2^{|A|}$, the $1$-entries of $Mz$ mark precisely the *odd rows* — the vertices of $B$ having $1$ or $3$ neighbors in $X$.

Delete one selected edge at each odd row and suppress every remaining vertex of $B$. Each vertex of $X$ originally sent $3$ edges to $B$, we deleted $|Mz|$ edges (where $|Mz|$ denotes Hamming weight, the number of $1$s), and each of the $|B|$ rows keeps at most $2$ edges. Counting the surviving edges gives the fundamental incidence bound:

$$
3|X| - |Mz| \le 2|B|.
$$

Furthermore, suppressing $B$ leaves a dyadic-cycle-free graph on $X$ whose vertices are cubic except for at most $|Mz|$ lost incidences. Let $c, p, q$ be positive integer lower bounds on the order of a connected dyadic-cycle-free graph whose vertices are cubic except for $0$, $1$, or $2$ degree-two vertices, respectively. The currently known values are:

* $c = 50$ ([Ducoffe and Dumitru, Theorem 5.1](https://arxiv.org/html/2609.28594v1#S5)),
* $p = 41$ and $q = 32$ ([Bridges.md](Bridges.md)).

For any nonempty $X \subseteq A$, counting the degree drops gives the following lower bounds on $|X|$:

| Odd rows ($\lvert Mz\rvert$) | Degrees lost on $X$ | Lower bound on $\lvert X\rvert$ |
| ---: | --- | ---: |
| 0 | None | $c$ |
| 1 | One vertex drops to degree two | $p$ |
| 2 | Two vertices each lose one, or one vertex loses two | $\min(q, p + 1)$ |

To verify the last row, consider the two ways two deleted edges can hit $X$:
* **Two distinct vertices lose one edge each:** If they lie in the same connected component of the suppressed graph, that component has at least $q$ vertices. If they lie in separate components, each component has one degree-two vertex and hence at least $p$ vertices, giving at least $2p \ge p + 1$ vertices combined.
* **Both deleted edges hit the same vertex $x \in X$:** Then $x$ becomes a degree-one leaf. Removing $x$ drops its sole neighbor's degree to two, leaving a one-terminal component of order at least $p$, so $|X| \ge p + 1$.

**Quick application.** When $M$ is square ($|A| = |B| = m$) and invertible over $\mathbf{F}_2$, taking $z = M^{-1} e_b$ for any standard basis vector $e_b$ gives $|Mz| = 1$, so $|X| \ge p = 41$. The incidence bound $3|X| - 1 \le 2m$ immediately forces $2m \ge 3p - 1 = 122$. Counting Hamming distances between pairs of columns of $M^{-1}$ improves this to **136** (see [BipartiteBounds.md](BipartiteBounds.md)).

---

## A cut inequality for arbitrary vertex sets

What if $A$ is *not* an independent set, or the counterexample is *not* cubic? Rather than relying on parity mod $2$, we can ask a direct combinatorial question: can we assign $3$ incident edges from each vertex of $A$ into the set of outside vertices that see $A$ at least twice, using each outside vertex at most twice? Max-flow/min-cut turns the failure of such an assignment into a quantitative cut inequality.

**Theorem.** Let $G$ be a minimum-order counterexample on $n$ vertices, take any nonempty proper subset $A \subsetneq V(G)$, and set $B = \{b \notin A : |N(b) \cap A| \ge 2\}$. Then some nonempty subset $T \subseteq A$ satisfies

$$
3|T| - \sum_{b \in B} \min(2, |N(b) \cap T|) \ge \begin{cases}
2, & \text{if } 2|A| < n, \\
1, & \text{if } 2|A| \ge n.
\end{cases}
$$

**Proof.** Build a directed flow network from a source $s$ through $A$ and $B$ to a sink $t$:
* directed edge $s \to a$ of capacity $3$ for each $a \in A$,
* directed edge $a \to b$ of capacity $1$ for each edge $ab$ of $G$ with $a \in A$ and $b \in B$,
* directed edge $b \to t$ of capacity $2$ for each $b \in B$.

Consider any $s$-$t$ cut whose source-side vertices in $A$ form a subset $T \subseteq A$. Every vertex $a \in A \setminus T$ contributes $3$ to the cut (cutting $s \to a$). Each vertex $b \in B$ can independently be placed on whichever side of the cut costs less: putting $b$ on the sink side cuts the $|N(b) \cap T|$ edges from $T$ to $b$, while putting $b$ on the source side cuts the capacity-$2$ edge $b \to t$. The minimum cut with source-side set $T \subseteq A$ therefore has capacity

$$
3(|A| - |T|) + \sum_{b \in B} \min(2, |N(b) \cap T|).
$$

By the max-flow min-cut theorem, the maximum *deficit*

$$
\Delta = \max_{T \subseteq A} \left(3|T| - \sum_{b \in B} \min(2, |N(b) \cap T|)\right)
$$

equals $3|A|$ minus the maximum integral flow value.

* **$\Delta = 0$ is impossible:** A full flow of value $3|A|$ selects a bipartite subgraph between $A$ and $B$ in which every vertex of $A$ has degree $3$ and every vertex of $B$ has degree $0, 1,$ or $2$. For each vertex $b \in B$ of degree $1$ in this subgraph, the definition of $B$ guarantees a second neighbor of $b$ in $A$; adding that edge brings $b$'s degree up to $2$ (and can only raise degrees in $A$). Suppressing $B$ then produces a dyadic-cycle-free graph on $A$ of minimum degree at least three, contradicting minimality of $G$.
* **$\Delta = 1$ is impossible when $2|A| < n$:** A maximum integral flow of value $3|A| - 1$ leaves every vertex of $A$ at degree $3$ except for a single vertex of degree $2$. Topping up singly used vertices of $B$ as above and suppressing $B$ leaves a dyadic-cycle-free graph on $A$ with at most one degree-two vertex. Applying the two-copy bridge repair from earlier yields a counterexample on at most $2|A| < n$ vertices, again contradicting minimality.

Finally, $T = \emptyset$ has deficit $0$, so any set $T \subseteq A$ attaining the positive lower bound must be nonempty. $\square$

### Worked example: $(3, 5)$-biregular bipartite graphs

Consider any nonempty bipartite graph whose one shore is cubic and whose opposite shore $A$ has minimum degree at least five. For any $T \subseteq A$, every cubic vertex $b$ outside $A$ has $|N(b) \cap T| \in \{0, 1, 2, 3\}$, and in all four cases one checks directly that

$$
\min(2, |N(b) \cap T|) \ge \frac{2}{3}|N(b) \cap T|.
$$

Summing over all $b$ outside $A$ gives

$$
\sum_{b} \min(2, |N(b) \cap T|) \ge \frac{2}{3} \sum_{a \in T} d(a) \ge \frac{10}{3}|T| \ge 3|T|.
$$

The maximum deficit is therefore $0$, so a full integral flow exists. Running the flow-and-suppression construction on any dyadic-cycle-free graph of this type produces a strictly smaller unrestricted counterexample on the vertex set $A$.
