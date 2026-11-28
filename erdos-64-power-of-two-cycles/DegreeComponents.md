# Degree-Three Components in a Minimal Counterexample

What does a *smallest* counterexample to Erdős Problem #64 look like? Pick a counterexample $G$ first with the fewest vertices, and among those with the fewest edges. Split its vertices into *light* (degree-three, or *cubic*) vertices $L$ and *heavy* (degree at least four) vertices $H$. Because deleting an edge between two heavy vertices preserves minimum degree three, every edge of $G$ must touch $L$ — so the heavy vertices form an independent set, and the light vertices organize into connected components that supply all edges into $H$.

Tracking how many edges each light component can send to $H$, together with how disjoint triangles behave when contracted, yields five sharp structural laws.

---

## Summary of results

Let $G$ be a finite simple graph of minimum degree at least three with no cycle of power-of-two length. Work either in the class of all graphs or in any subgraph-closed class containing such a graph, and pick $G$ first with the fewest vertices and then with the fewest edges. Write:

* $L$ for the degree-three (*light* / *cubic*) vertices of $G$, with $\ell = |L|$,
* $H$ for the vertices of degree at least four (*heavy*), with $h = |H|$,
* $n = \ell + h$ for the total order of $G$.

Then:

* **Disjoint triangles and claws (unrestricted):** Every set of vertex-disjoint triangles misses at least two cubic vertices, and $G$ contains an induced claw ($K_{1,3}$).
* **Triangle-free class:** $\ell \ge 8n/11$.
* **Bipartite class:** $\ell \ge 20n/27$.
* **Girth at least $g \ge 3$:** $\ell \ge 4(g - 1)n / (5g - 3)$ in any subgraph-closed class where $G$ has girth at least $g$.
* **Additive cubic-density bound (unrestricted):** $\ell \ge 2h + 8$ (equivalently $3\ell \ge 2n + 8$). This last bound uses the published verification through order $40$ together with the 11-vertex calculation below.

The first three proportion bounds also apply to a globally minimal counterexample if it happens to have that property. Working inside the bipartite class separately lets us bound the smallest bipartite counterexample even if a smaller nonbipartite counterexample exists.

---

## Counting incidences across a cubic component

**The big idea.** Every heavy vertex needs at least $4$ edges coming from $L$. How generously can a connected component $C$ of $G[L]$ feed edges into $H$? A connected graph on $s$ vertices has at least $s - 1$ internal edges, leaving at most $3s - 2(s - 1) = s + 2$ edges to send to $H$. Larger components therefore supply fewer edges per light vertex — so forcing every component of $G[L]$ to have size at least $k$ immediately forces a large fraction of $G$ to lie in $L$.

First note two elementary minimality properties (Lemma 3.2 in [Ducoffe and Dumitru](https://arxiv.org/html/2609.28594v1#S3)):

1. **Every edge of $G$ has an endpoint in $L$:** Deleting an edge between two vertices of $H$ preserves minimum degree three and strictly decreases the edge count.
2. **Every vertex in $L$ has a neighbor in $L$:** Deleting a cubic vertex whose neighbors all lie in $H$ leaves every remaining vertex with degree at least three, contradicting vertex-minimality.

Now assume $h > 0$ (if $h = 0$, then $\ell = n$ and all ratio bounds hold trivially), and let $C$ be any connected component of $G[L]$. Deleting $C$ leaves a nonempty graph in which every remaining vertex of $L$ keeps all three of its neighbors. By minimality, some vertex $v \in H$ must drop to degree at most two after deleting $C$, which forces

$$
|N(v) \cap C| \ge d_G(v) - 2 \ge 2.
$$

Join two neighbors of $v$ in $C$ by a shortest path inside $C$, say of length $d$ edges. Together with $v$, this path closes a simple cycle of length $d + 2$:

* Since $G$ has no $4$-cycle, $d \ne 2$.
* In a **triangle-free** graph, $d \ne 1$ as well, forcing $d \ge 3$ and hence $|C| \ge 4$.
* In a **bipartite** graph, $d$ must be even (both neighbors of $v$ lie in the same shore) and $d \ne 2$, forcing $d \ge 4$ and hence $|C| \ge 5$.
* In general, **girth at least $g$** forces $d + 2 \ge g$, so $|C| \ge d + 1 \ge g - 1$.

Now count edges crossing between $L$ and $H$. A component $C$ of $G[L]$ on $s$ vertices with $e(C)$ internal edges sends $3s - 2e(C)$ edges to $H$. Because $C$ is connected, $e(C) \ge s - 1$, so it sends at most $s + 2$ edges to $H$. If every component of $G[L]$ has order at least $k$, then each component sends at most $s + 2 \le s(1 + 2/k)$ edges to $H$. Summing over all components gives

$$
4h \le \sum_{v \in H} d_G(v) \le \ell + \frac{2\ell}{k}.
$$

Substituting $h = n - \ell$ and solving for $\ell / n$ yields

$$
\frac{\ell}{n} \ge \frac{4k}{5k + 2}.
$$

Plugging in $k = 4$, $k = 5$, and $k = g - 1$ gives $8/11$, $20/27$, and $4(g - 1)/(5g - 3)$, respectively.

---

## The unrestricted tradeoff with triangles

Without a girth restriction, components of $G[L]$ can have size $2$ or $3$ — and those are the *only* components that can send more than $3s/2$ edges to $H$. Write $c_i$ for the number of components of $G[L]$ of order $i$, and define the heavy degree excess $S = \sum_{v \in H}(d_G(v) - 4) \ge 0$.

* Any component of size $s \ge 4$ sends at most $s + 2 \le 3s/2$ edges to $H$.
* A component of size $2$ sends at most $4 = 3(2)/2 + 1$ edges to $H$.
* A component of size $3$ sends at most $5 = 3(3)/2 + 1/2$ edges to $H$.

Summing over all components and multiplying by $2$ gives

$$
8h + 2S \le 3\ell + 2c_2 + c_3,
\qquad
8n + 2S \le 11\ell + 2c_2 + c_3.
$$

Every component counted by $c_2$ or $c_3$ supplies two light vertices of a **triangle through a heavy vertex**: the shortest path of length $d$ between two neighbors of $v \in H$ inside $C$ satisfies $d \le |C| - 1 \le 2$ and $d \ne 2$, which forces $d = 1$.

### Size-two components give vertex-disjoint triangles

Zoom in on a size-two component $xy$ of $G[L]$, together with its common heavy neighbor $v \in H$:

1. Because $v$ drops to degree at most $2$ when $\{x, y\}$ is deleted and has only $2$ neighbors in $\{x, y\}$, we must have $d_G(v) = 4$.
2. The other two heavy neighbors $a, b \in H$ of $x$ and $y$ are distinct, because if $x$ and $y$ shared two heavy neighbors $v$ and $a$, then $v x a y v$ would be a $4$-cycle. (This local description of a size-two component was also proved by [Andrew Bisch](https://ajbisch.github.io/papers/erdos-gyarfas.html).)
3. **No heavy vertex $v$ can witness two size-two components:** Otherwise all four neighbors of $v$ would lie in those two components, and their four outer heavy neighbors would have to be pairwise distinct (any repeated outer neighbor would share two neighbors with $v$, forming a $4$-cycle). Deleting $v$ and both size-two components would then lower each outer heavy neighbor's degree by just $1$ (keeping it at least $3$) and leave every other remaining vertex untouched — contradicting minimality!

The $c_2$ triangles coming from size-two components are therefore **vertex-disjoint**.

### Stability bound

Comparing every component against $5s/3$ instead of $3s/2$: any component of size $s \ge 3$ sends at most $s + 2 \le 5s/3$ edges to $H$, while a size-two component sends $4$. Multiplying the edge count by $3$ gives $12h + 3S \le 5\ell + 2c_2$. Setting $E = \ell - 2h = 3\ell - 2n$ (so $3h = n - E$ and $3\ell = 2n + E$), multiplying by $3$, and rearranging gives

$$
3c_2 \ge n - \frac{17}{2}E + \frac{9}{2}S.
$$

In particular, whenever $\ell/n \le 2/3 + \varepsilon$ (so $E \le 3\varepsilon n$), the vertex-disjoint triangles arising from size-two components cover at least $(1 - 51\varepsilon/2)n$ vertices of $G$.

---

## Contracting disjoint triangles

**The big idea.** Contracting a collection of vertex-disjoint triangles into single vertices shrinks $G$ to a smaller graph $Q$ while keeping minimum degree three. By minimality, $Q$ has a power-of-two cycle of length $r$. Can we lift that cycle to a cycle of length $2r$ (the next power of two!) back in $G$? Whenever the quotient cycle enters a triangle at one corner and leaves at a *different* corner, we have a choice: walk across the triangle in **1 edge** (directly) or **2 edges** (via the third corner). Every other visit — at an uncovered vertex, or entering and leaving a triangle through the *same* corner — uses **0 internal edges**. As long as at most half the visits use $0$ internal edges, we simply take $2$ internal edges at enough two-corner visits to bring the total number of internal edges up to $r$, doubling the cycle length to $2r$!

**Theorem.** In a globally minimal counterexample, every collection of vertex-disjoint triangles leaves at least two cubic vertices uncovered.

**Proof.** Take $t$ vertex-disjoint triangles in $G$ and contract each triangle to a single vertex (leaving all uncovered vertices as singletons) to form a quotient graph $Q$.

1. **$Q$ is simple and has minimum degree at least three:**
   * No two blocks can be joined by parallel edges: two parallel edges with distinct endpoints on both sides would form a $4$-cycle using $1$ edge from each triangle, while two parallel edges sharing an endpoint on one side would form a $4$-cycle using the $2$-edge path through the opposite triangle.
   * Every singleton keeps its original degree ($\ge 3$). Every contracted triangle has degree at least $3$ because each of its three corners has at least one external edge — and degree at least $4$ if any of its corners is heavy.

   *(Warm-up: contracting a single triangle produces a smaller graph with a power-of-two cycle by minimality. That cycle must traverse the contracted vertex via two different corners — otherwise it lifts unchanged to $G$. Opening it at the contracted vertex yields a path of the same power-of-two length between two corners of the triangle, with all internal vertices outside it.)*

2. **The cycle-doubling lift:** Consider any simple cycle of length $r$ in $Q$. At each visit to a triangle through two different corners, we can route through $1$ or $2$ internal edges; every other visit uses $0$ internal edges. Suppose the number $z$ of zero-edge visits satisfies $z \le r/2$. Pick $z$ of the $r - z$ two-corner visits and route them through $2$ internal edges, and route the remaining $r - 2z$ two-corner visits through $1$ internal edge. That adds $2z + (r - 2z) = r$ internal edges to the $r$ external edges of the quotient cycle, lifting to a simple cycle of length $2r$ in $G$ (simplicity holds because each block is visited at most once). In particular, whenever zero-edge visits are never consecutive along the cycle, we can simply take $2$ internal edges at the visit immediately following each zero-edge visit. This isolated-zero cycle lift is formalized in [Erdos64/TrianglePacking.lean](Erdos64/TrianglePacking.lean).

3. **Ruling out zero uncovered cubic vertices:** Suppose for contradiction that our triangle packing misses at most one cubic vertex. Because $G$ has at least four cubic vertices (either all vertices are cubic, or some heavy vertex has at least four cubic neighbors), the packing is nonempty ($t \ge 1$). Thus $Q$ has strictly fewer vertices than $G$ and must contain a power-of-two cycle.
   * Notice that a zero-edge visit *inside a triangle* enters and leaves through the same corner, giving that corner at least two external edges (plus its two triangle edges) — so that corner must be **heavy**.
   * If every uncovered vertex is heavy, then *every* zero-edge visit occurs at a heavy vertex. Because heavy vertices form an independent set in $G$, no two zero-edge visits can be consecutive on the cycle, forcing $z \le r/2$ and lifting to a $2r$-cycle in $G$ — a contradiction.

4. **Ruling out a single uncovered cubic vertex $u$:** Suppose instead that $u$ is the unique uncovered cubic vertex. To avoid the doubling lift, every power-of-two cycle in $Q$ (of even length $r$) must satisfy $z > r/2$, which forces at least $2z - r \ge 2$ edges of the cycle to join consecutive zero-edge visits. Because heavy vertices are independent, every such edge must be incident to $u$. Hence:
   * Every power-of-two cycle in $Q$ passes through $u$, so $Q - u$ has **no power-of-two cycle**.
   * Along any such cycle, both neighbors of $u$ on the cycle are distinct blocks containing a heavy vertex — each of which has degree at least $4$ in $Q$.

   Since $u$ has degree $3$ in $Q$ and at least two of its neighbors have degree at least $4$, deleting $u$ leaves $Q - u$ with **at most one degree-two vertex**. If $Q - u$ has a degree-two vertex, take two disjoint copies of $Q - u$ and connect their degree-two vertices by a bridge (which no cycle can cross). Either way, we obtain a counterexample on at most $2(t + h)$ vertices, where $h$ counts the uncovered heavy vertices.

   Finally, count edges leaving the $h$ uncovered heavy vertices in $G$. Their at least $4h$ incident edges must all go to $u$ or to cubic corners of the $t$ triangles. Each cubic corner has only $1$ external edge and $u$ has $3$ edges, so $4h \le 3 + 3t$. Since $t \ge 1$, this gives $4(h - t) \le 3 - t \le 2$, forcing $h \le t$. Therefore

   $$
   2(t + h) \le 3t + h < 3t + h + 1 = |G|,
   $$

   contradicting the minimality of $G$. $\square$

### Triangle factors and cubic graphs

* **General counterexamples with a triangle factor ($\ge 126$ vertices):** If a counterexample has a *triangle factor* (a partition of all vertices into vertex-disjoint triangles), repeatedly delete any edge between two distinct triangles whose endpoints are both heavy. This preserves both the triangle factor and minimum degree three. Contracting all triangles then works by the exact same isolated-zero doubling argument (consecutive vertices on any quotient cycle are connected by an edge between distinct triangles, which cannot join two heavy vertices), yielding a counterexample on one third as many vertices. Combining this with the [order-42 lower bound](Order41.md) shows that every counterexample with a triangle factor has at least **$3 \cdot 42 = 126$ vertices**.
* **Cubic counterexamples with a triangle factor ($\ge 150$ vertices):** When the counterexample is cubic, its contracted quotient is also cubic, and every cubic counterexample has at least $50$ vertices ([Ducoffe and Dumitru, Theorem 5.1](https://arxiv.org/html/2609.28594v1#S5)), forcing at least **$3 \cdot 50 = 150$ vertices**. (Salehi Nowbandegani, Esfandiari, Shirdareh Haghighi, and Bibak proved that the cubic triangle-factor lift actually produces every cycle length from $2r$ to $3r$ and deduced a lower bound of $114$ for cubic claw-free counterexamples; see [Proposition 6, Corollary 7, and Theorem 9](https://arxiv.org/pdf/1109.5398#page=5).)
* **Uncovered edges in a smallest cubic counterexample:** Any smallest cubic counterexample contains **at least two edges whose endpoints lie on no triangle**. Its triangles are automatically vertex-disjoint (two triangles meeting at a cubic vertex would share an edge and form a $4$-cycle). If the graph has any triangle at all, contract all triangles to obtain a smaller cubic graph. On a power-of-two cycle in this quotient, only uncovered vertices cause zero-edge visits; to escape doubling, more than half the vertices on the even-length cycle must be uncovered, forcing at least two edges joining uncovered vertices.

---

## An induced claw in a globally minimal counterexample

**The big idea.** An *induced claw* is $K_{1,3}$ — a center vertex adjacent to three pairwise nonadjacent neighbors. If a minimal counterexample $G$ avoids both $4$-cycles and induced claws, every vertex's neighborhood is so tightly constrained that $G$ breaks cleanly into triangles joined only at shared degree-four corners or by single external edges. Turning each triangle into a vertex produces a strictly smaller cubic graph whose power-of-two cycles lift right back to doubled cycles in $G$.

**Theorem.** Every globally minimal counterexample contains an induced claw.

**Proof.** Suppose for contradiction that a globally minimal counterexample $G$ has no induced claw.

1. **Rigid triangle structure:** Inside the neighborhood $N(v)$ of any vertex $v$, two adjacent edges would form a $4$-cycle through $v$, so $N(v)$ consists of a matching plus isolated vertices. Because $G$ is claw-free, $N(v)$ has independence number at most $2$. That rules out degree $5$ or higher (any matching plus isolated vertices on $\ge 5$ vertices has an independent set of size $\ge 3$). Hence:
   * Every cubic vertex has a single edge in its neighborhood and therefore lies in **exactly one triangle**.
   * Every heavy vertex has degree $4$, with a two-edge matching in its neighborhood, and therefore lies in **exactly two triangles**.
   * Because heavy vertices form an independent set, **no triangle contains two heavy vertices**.

2. **The triangle-link graph $K$:** Build a graph $K$ with one vertex for each triangle of $G$. Join two triangles by an edge in $K$ whenever they share a heavy corner, and also join the triangles at the two ends of every external edge between cubic vertices. Each triangle has three corners, each contributing one incident link, so every vertex of $K$ has degree $3$.

   Moreover, $K$ is **simple**:
   * Two shared corners between the same pair of triangles would give a $4$-cycle.
   * Two external links at cubic corners between the same pair of triangles would give a $4$-cycle.
   * A shared heavy corner $v$ combined with an external cubic link $xy$ between the same two triangles would give the $4$-cycle $z - x - y - v - z$, where $z$ is the third corner of $x$'s triangle (since $z$ is adjacent to both $x$ and $v$, and $y$ is adjacent to both $x$ and $v$).

   Thus $K$ is simple and cubic. Because every triangle has $3$ vertices while every vertex of $G$ lies in at most $2$ triangles, double-counting vertex-triangle incidences gives $3|V(K)| \le 2|V(G)|$, so $|V(K)| < |V(G)|$.

3. **Lifting power-of-two cycles:** By minimality, $K$ contains a power-of-two cycle of length $r$. Orient this cycle. Moving between consecutive triangles uses **1 edge** of $G$ at an external cubic link and **0 edges** at a shared heavy corner. Inside each triangle along the cycle, walk **1 edge** directly from entry corner to exit corner — *except* immediately after entering through a shared heavy corner, where we take the **2-edge** route through the triangle's third corner.

   Each transition plus the following triangle contributes $1 + 1 = 2$ edges (for an external link) or $0 + 2 = 2$ edges (for a shared heavy corner), for a total length of **$2r$**! To check simplicity: whenever we detour through a third corner after entering at a shared heavy corner, that third corner is cubic (since no triangle has two heavy vertices) and belongs to no other triangle, so detour vertices never repeat; meanwhile each shared heavy corner appears only at the single junction between the two consecutive triangles that share it. This lifts the $r$-cycle in $K$ to a simple $2r$-cycle in $G$, a contradiction. Therefore $G$ must contain an induced claw. $\square$

---

## Independent check of the additive bound for a globally minimal counterexample

An August 2026 preprint proves $\ell \ge 2h + 8$ as Theorem 1 and $\ell \ge 2h + 10$ for $h \ge 14$ as Theorem 2 ([*Additive Cubic-Density Constraints on Minimal Counterexamples*, Theorems 1 and 2](https://airaxiv.com/papers/pdf/2608.0018/?t=1786961842&v=1)). The argument below independently checks its 11-vertex calculation and pairs it with the later order-40 verification.

### The 2-degenerate auxiliary graph $M$

Let $G$ be minimal in the class of all graphs, and partition the cubic vertices $L = L_0 \sqcup L_1 \sqcup L_2$ according to how many heavy neighbors each cubic vertex has (recall that no cubic vertex has $3$ heavy neighbors). Build an auxiliary graph $M$ on vertex set $H$ by turning each vertex of $L_2$ into an edge joining its two heavy neighbors (the auxiliary graph of Lemma 3.5 in [Ducoffe and Dumitru](https://arxiv.org/html/2609.28594v1#S3.SS2)):

* $M$ is **simple** (parallel edges would correspond to two $L_2$-vertices sharing both heavy neighbors, forming a $4$-cycle in $G$).
* Every $r$-cycle in $M$ lifts to a $2r$-cycle in $G$ via its distinct $L_2$-vertices, so $M$ has **no power-of-two cycle**.
* No subgraph of $M$ can have minimum degree at least three (it would be a strictly smaller counterexample on at most $h < n$ vertices), so every nonempty subgraph of $M$ contains a vertex of degree at most $2$ — i.e., $M$ is **2-degenerate**.

Define the edge deficit $D = 2h - e(M)$. Counting incidences at $H$ gives $|L_1| + 2|L_2| = 4h + S$, where $S = \sum_{v \in H}(d_G(v) - 4)$ and $e(M) = |L_2|$. Subtracting $|L_2| = e(M)$ and adding $|L_0|$ yields

$$
\ell - 2h = D + S + |L_0|.
$$

Furthermore, the handshaking lemma gives $2e(G) = 3\ell + 4h + S$, so

$$
\ell - 2h \equiv S \pmod 2.
$$

### Bounding $D$ via an 11-vertex suffix check

Repeatedly deleting a vertex of degree $j \le 2$ from $M$ changes $2|V| - |E|$ by $-2 + j \le 0$, so $2|V| - |E|$ can only **decrease** along a 2-degeneracy deletion order. If $h \ge 11$, keep the last $11$ vertices in such a deletion order. As verified below, every 11-vertex 2-degenerate graph with no $4$- or $8$-cycle has at most $15$ edges, so its deficit is at least $2(11) - 15 = 7$, forcing $D \ge 7$.

Because [Ducoffe and Dumitru (Theorem 5.1)](https://arxiv.org/html/2609.28594v1#S5) verified the conjecture through order $40$, we have $n \ge 41$. Suppose for contradiction that $\ell - 2h \le 7$. Then $41 \le n = 3h + (\ell - 2h) \le 3h + 7$ forces $3h \ge 34$, hence $h \ge 12 \ge 11$ and therefore $D \ge 7$. The identity $\ell - 2h = D + S + |L_0|$ then pins down $\ell - 2h = D = 7$ and $S = |L_0| = 0$ — contradicting $\ell - 2h \equiv S \pmod 2$! Thus $\ell \ge 2h + 8$.

### Reproducing the eleven-vertex check

Build the graph in *reverse* deletion order, where each new vertex connects to $j \le 2$ earlier vertices. Adding a vertex with $j$ earlier neighbors increases the deficit $2|V| - |E|$ by $2 - j \ge 0$, so any 11-vertex graph with at least $16$ edges (deficit at most $6$) must stay at deficit at most $6$ throughout its entire construction. A new vertex attached to two earlier vertices $a$ and $b$ closes a $4$- or $8$-cycle if and only if an earlier simple path of length $2$ or $6$ joins $a$ and $b$. The program [scripts/degree_suffix.cpp](scripts/degree_suffix.cpp) enumerates every valid ordered construction without isomorphism pruning:

```sh
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror scripts/degree_suffix.cpp -o /tmp/erdos64-degree-suffix
/tmp/erdos64-degree-suffix
```

For orders $0$ through $11$, the counts of valid ordered constructions are:

$$
1,\ 1,\ 2,\ 8,\ 43,\ 277,\ 1942,\ 14700,\ 107127,\ 520851,\ 783924,\ 0.
$$

This C++ verification is independent of the Lean forbidden-induced-path proofs in this package.
