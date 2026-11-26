# Degree-three components in a minimal counterexample

Let $G$ be a finite simple graph of minimum degree at least three with no cycle of power-of-two length. Work either in the class of all graphs or in any subgraph-closed class containing such a graph, and pick $G$ first with the fewest vertices and then with the fewest edges. Write $L$ for the degree-three vertices of $G$ and $H$ for its vertices of degree at least four, with $\ell = |L|$, $h = |H|$, and $n = \ell + h$.

* In the unrestricted class, every set of vertex-disjoint triangles misses at least two cubic vertices, and $G$ contains an induced claw.
* In the triangle-free class, $\ell \ge 8n/11$.
* In the bipartite class, $\ell \ge 20n/27$.
* In any subgraph-closed class where $G$ has girth at least $g \ge 3$, $\ell \ge 4(g - 1)n/(5g - 3)$.
* In the class of all graphs, $\ell \ge 2h + 8$ (equivalently $3\ell \ge 2n + 8$). This last bound uses the published verification through order 40 together with the 11-vertex calculation below.

The first three proportion bounds also apply to a globally minimal counterexample if it happens to have that property. Working inside the bipartite class separately lets us bound the smallest bipartite counterexample even if a smaller nonbipartite counterexample exists.

## Counting incidences across a cubic component

Every edge of $G$ has an endpoint in $L$, because deleting an edge between two vertices of $H$ keeps minimum degree three. Likewise, every vertex in $L$ has a neighbor in $L$, because deleting a cubic vertex whose neighbors all lie in $H$ leaves every neighbor with degree at least three. Both deletion arguments appear as Lemma 3.2 in [Ducoffe and Dumitru](https://arxiv.org/html/2609.28594v1#S3).

Assume $h > 0$ (if $h = 0$, the ratio bounds hold immediately). Let $C$ be a connected component of $G[L]$. Deleting $C$ leaves a nonempty graph in which every remaining vertex of $L$ keeps all three neighbors. By minimality, some vertex $v \in H$ must drop to degree at most two after deleting $C$, so

$$
|N(v) \cap C| \ge d_G(v) - 2 \ge 2.
$$

Join two neighbors of $v$ in $C$ by a shortest path in $C$, say of length $d$ edges. Together with $v$, this forms a simple cycle of length $d + 2$, so $d \ne 2$. In a triangle-free graph, $d \ne 1$ as well, forcing $|C| \ge 4$. In a bipartite graph, $d$ is even, so $|C| \ge 5$. In general, girth at least $g$ forces $|C| \ge g - 1$.

If $C$ has $s$ vertices and $e(C)$ edges, it sends $3s - 2e(C)$ edges to $H$. Since $C$ is connected, $e(C) \ge s - 1$, so it sends at most $s + 2$ edges to $H$. If every component of $G[L]$ has order at least $k$, summing over all components gives

$$
4h \le \sum_{v \in H} d_G(v) \le \ell + \frac{2\ell}{k},
\qquad
\frac{\ell}{n} \ge \frac{4k}{5k + 2}.
$$

Setting $k = 4, 5, g - 1$ yields the stated bounds.

## The unrestricted tradeoff with triangles

Write $c_i$ for the number of components of $G[L]$ of order $i$, and put $S = \sum_{v \in H}(d_G(v) - 4)$. A component of order $s \ge 4$ sends at most $3s/2$ edges to $H$, while components of order 2 and 3 send at most 4 and 5 edges. Counting edges between $L$ and $H$ gives

$$
8h + 2S \le 3\ell + 2c_2 + c_3,
\qquad
8n + 2S \le 11\ell + 2c_2 + c_3.
$$

Every component counted by $c_2$ or $c_3$ contains two light vertices of a triangle through a heavy vertex, because the shortest path constructed above has length at most 2 and cannot have length 2.

For a size-two component $xy$, its common heavy neighbor $v$ has degree four. Its other two heavy neighbors $a, b$ are distinct, since sharing two heavy neighbors would create a 4-cycle. This local description of a size-two component was also proved by [Andrew Bisch](https://ajbisch.github.io/papers/erdos-gyarfas.html). No heavy vertex can witness two size-two components: otherwise its four neighbors would all lie in those two components, and their four outer heavy neighbors would be pairwise distinct (any repetition would share two neighbors with $v$, forming a 4-cycle). Deleting $v$ and both components would then reduce each outer heavy neighbor's degree by one and leave every other remaining vertex unchanged, contradicting minimality. The $c_2$ triangles are therefore vertex-disjoint.

Size-two components also yield a stability bound. Any component of size $s \ge 3$ sends at most $5s/3$ edges to $H$, while a size-two component sends 4. Hence $12h + 3S \le 5\ell + 2c_2$. Setting $E = \ell - 2h = 3\ell - 2n$ gives

$$
3c_2 \ge n - \frac{17}{2}E + \frac{9}{2}S.
$$

In particular, if $\ell/n \le 2/3 + \varepsilon$, the vertex-disjoint triangles coming from size-two components cover at least $(1 - 51\varepsilon/2)n$ vertices.

## Contracting disjoint triangles

**Theorem.** In a globally minimal counterexample, every collection of vertex-disjoint triangles leaves at least two cubic vertices uncovered.

Take $t$ vertex-disjoint triangles in $G$ and contract each to a single vertex, leaving all uncovered vertices as singletons, to form a quotient graph $Q$. Then $Q$ is simple: two parallel edges between blocks with distinct ends on both sides would form a 4-cycle using one edge from each triangle, and two parallel edges sharing one end would form a 4-cycle with the two-edge path through the opposite triangle. Every singleton keeps its original degree, and every contracted triangle has degree at least three because each corner has an external edge (and degree at least four if any corner is heavy).

As a warm-up, contracting a single triangle gives a smaller graph that has a power-of-two cycle by minimality. That cycle must pass through the contracted vertex using two different corners (otherwise it already lifts unchanged to $G$). Opening it at the contracted vertex gives a path of the same power-of-two length between two corners of the triangle, with all internal vertices outside it.

Now consider any cycle of length $r$ in $Q$. When the cycle visits a triangle at two different corners, we can cross that triangle using either 1 or 2 internal edges. Every other visit uses 0 internal edges. If the number $z$ of zero-edge visits satisfies $z \le r/2$, take 2 edges at $z$ of the $r - z$ two-corner visits and 1 edge at the rest. That uses $r$ internal edges and $r$ external edges, lifting to a simple cycle of length $2r$ in $G$ (each block is visited at most once). In particular, whenever zero-edge visits are never consecutive on the cycle, the visit right after each zero can add the extra edge. This isolated-zero cycle lift is formalized in [Erdos64/TrianglePacking.lean](Erdos64/TrianglePacking.lean).

Suppose for contradiction that our triangle packing misses at most one cubic vertex. Because $G$ has at least four cubic vertices (either all vertices are cubic, or some heavy vertex has at least four cubic neighbors), the packing is nonempty. Thus $Q$ has fewer vertices than $G$ and contains a power-of-two cycle. A zero-edge visit inside a triangle uses a corner with at least two external edges, which must be heavy. If every uncovered vertex is heavy, then every zero-edge visit is heavy, so no two are consecutive (heavy vertices are independent), and doubling the cycle length gives a contradiction.

Suppose instead that $u$ is the unique uncovered cubic vertex. To escape the doubling lift, every power-of-two cycle in $Q$ must satisfy $z > r/2$. Because $r$ is even, the cycle has at least $2z - r \ge 2$ edges joining consecutive zero-edge visits. Heavy vertices are independent, so every such edge must hit $u$. Hence every power-of-two cycle passes through $u$, and along one such cycle both neighbors of $u$ are distinct blocks containing a heavy vertex, each having degree at least four in $Q$.

Therefore $Q - u$ has no power-of-two cycle and at most one degree-two vertex (since $u$ had degree three). If $Q - u$ has a degree-two vertex, take two copies of $Q - u$ and join their degree-two vertices by a bridge (which no cycle can use). Either way we obtain a counterexample on at most $2(t + h)$ vertices, where $h$ counts the uncovered heavy vertices. Their at least $4h$ incident edges go to $u$ or to cubic corners of the $t$ triangles. Each cubic corner has just one external edge, so $4h \le 3 + 3t$, which forces $h \le t$. Thus $2(t + h) < 3t + h + 1 = |G|$, contradicting minimality.

### Triangle factors and cubic graphs

If a counterexample has a triangle factor (a partition of all vertices into triangles), repeatedly delete any edge between two distinct triangles whose endpoints both have degree at least four. This keeps the triangle factor and minimum degree three. Contracting all triangles then works by the same argument, since consecutive vertices on a quotient cycle are joined by edges between distinct triangles, producing a counterexample on one third as many vertices. Combining this with the [order-42 lower bound](Order41.md) shows that any counterexample with a triangle factor has at least **126 vertices**.

A cubic counterexample with a triangle factor has at least **150 vertices**, because its quotient is cubic and every cubic counterexample has at least 50 vertices ([Ducoffe and Dumitru, Theorem 5.1](https://arxiv.org/html/2609.28594v1#S5)). Salehi Nowbandegani, Esfandiari, Shirdareh Haghighi, and Bibak proved that the cubic triangle-factor lift produces every cycle length from $2r$ to $3r$ and deduced a lower bound of 114 for cubic claw-free counterexamples ([Proposition 6, Corollary 7, and Theorem 9](https://arxiv.org/pdf/1109.5398#page=5)).

Any smallest cubic counterexample also has at least two edges whose endpoints lie on no triangle. Its triangles are vertex-disjoint, because two triangles meeting at a cubic vertex would share an edge and form a 4-cycle. If the graph has any triangle, contract all triangles to get a smaller cubic graph. On a power-of-two cycle in this quotient, only uncovered vertices give zero-edge visits. To avoid doubling, more than half the vertices on the cycle must be uncovered; since the cycle has even length, at least two edges join uncovered vertices.

## An induced claw in a globally minimal counterexample

Suppose a globally minimal counterexample $G$ has no induced claw. In any vertex neighborhood, two adjacent edges would form a 4-cycle through the center, so the neighborhood consists of a matching and isolated vertices. Because $G$ is claw-free, the neighborhood has independence number at most two, which rules out degree five or more. Every cubic vertex therefore lies in one triangle, every heavy vertex has degree four and lies in two triangles, and no triangle contains two heavy vertices.

Form a graph $K$ with one vertex per triangle of $G$: join two triangles by an edge whenever they share a heavy corner, and join the triangles at the two ends of every external edge between cubic vertices. Each triangle has three incident links, one at each corner. Then $K$ is simple: two shared corners between the same pair of triangles would give a 4-cycle, two links at cubic corners would give a 4-cycle, and a shared corner $v$ combined with an external link $xy$ would give a 4-cycle using the third corner of $x$'s triangle, $v$, and $y$. Thus $K$ is simple and cubic. Since every vertex of $G$ lies in at most two triangles while each triangle has three vertices, $K$ has fewer vertices than $G$.

Orient a cycle of length $r$ in $K$. Moving between consecutive triangles takes 1 edge at an external link and 0 edges at a shared heavy corner. Inside each triangle, take 1 edge along the cycle, except right after a shared corner, where we take the 2-edge route through its third corner. That third corner is cubic and belongs to no other triangle (since the entry corner is heavy), so these extra vertices never repeat, and every shared corner appears only at the junction of its two consecutive triangles. This yields a simple cycle of length $2r$ in $G$. By minimality, $K$ has a power-of-two cycle, which lifts to one in $G$. Thus $G$ must contain an induced claw.

## Independent check of the additive bound for a globally minimal counterexample

An August 2026 preprint proves $\ell \ge 2h + 8$ as Theorem 1 and $\ell \ge 2h + 10$ for $h \ge 14$ as Theorem 2 ([*Additive Cubic-Density Constraints on Minimal Counterexamples*, Theorems 1 and 2](https://airaxiv.com/papers/pdf/2608.0018/?t=1786961842&v=1)). The argument below independently checks its 11-vertex calculation and pairs it with the later order-40 verification.

Let $G$ be minimal in the class of all graphs, and partition $L$ into $L_0, L_1, L_2$ by the number of heavy neighbors. Build an auxiliary graph $M$ on $H$ by turning each vertex of $L_2$ into an edge joining its two heavy neighbors. Then $M$ is simple (parallel edges would form a 4-cycle in $G$), and every $r$-cycle in $M$ lifts to a $2r$-cycle in $G$ via its distinct vertices in $L_2$, so $M$ has no power-of-two cycle. No subgraph of $M$ can have minimum degree three (it would be a smaller counterexample), so every nonempty subgraph of $M$ has a vertex of degree at most two. This is the auxiliary graph of Lemma 3.5 in [Ducoffe and Dumitru](https://arxiv.org/html/2609.28594v1#S3.SS2).

Set $D = 2h - e(M)$. Counting incidences at $H$ gives $|L_1| + 2|L_2| = 4h + S$, with $e(M) = |L_2|$, so

$$
\ell - 2h = D + S + |L_0|.
$$

Also $2e(G) = 3\ell + 4h + S$, so $\ell - 2h \equiv S \pmod 2$.

Repeatedly deleting a vertex of degree at most two can only decrease $2|V| - |E|$. If $h \ge 11$, keep the last 11 vertices in such a deletion order. As verified below, an 11-vertex 2-degenerate graph with no 4- or 8-cycle has at most 15 edges, so its deficit is at least 7, giving $D \ge 7$.

Because [Ducoffe and Dumitru (Theorem 5.1)](https://arxiv.org/html/2609.28594v1#S5) verified the conjecture through order 40, we have $n \ge 41$. If $\ell - 2h \le 7$, then $n = 3h + (\ell - 2h)$ forces $h \ge 12$ and hence $D \ge 7$. The identity above then forces $\ell - 2h = D = 7$ and $S = |L_0| = 0$, contradicting $\ell - 2h \equiv S \pmod 2$.

### Reproducing the eleven-vertex check

Build the graph in reverse deletion order, where each new vertex connects to at most two earlier vertices. Adding a vertex with $j$ earlier neighbors raises the deficit $2|V| - |E|$ by $2 - j$, so any 11-vertex graph with at least 16 edges stays at deficit at most 6 throughout its construction. A new vertex with earlier neighbors $a, b$ closes a 4- or 8-cycle if and only if an earlier simple path of length 2 or 6 joins $a$ and $b$. The program [scripts/degree_suffix.cpp](scripts/degree_suffix.cpp) enumerates every valid ordered construction without isomorphism pruning:

~~~sh
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror scripts/degree_suffix.cpp -o /tmp/erdos64-degree-suffix
/tmp/erdos64-degree-suffix
~~~

For orders 0 through 11, the counts are $1, 1, 2, 8, 43, 277, 1942, 14700, 107127, 520851, 783924, 0$. This C++ verification is independent of the Lean forbidden-induced-path proofs in this package.
