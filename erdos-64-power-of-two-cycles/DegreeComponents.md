# Degree-three components in a minimal counterexample

Let $G$ be a finite simple graph of minimum degree at least three with no cycle of power-of-two length. Work in the class of all graphs, or in any class closed under taking subgraphs that contains such a graph. Choose $G$ first with the fewest vertices in that class, then with the fewest edges. Write $L$ for its degree-three vertices and $H$ for its vertices of degree at least four, with $\ell=|L|$, $h=|H|$ and $n=\ell+h$.

* In the unrestricted class, every collection of disjoint triangles misses at least two cubic vertices, and $G$ contains an induced claw.
* In the triangle-free class, $\ell\ge 8n/11$.
* In the bipartite class, $\ell\ge 20n/27$.
* In any such class in which $G$ has girth at least $g\ge3$, $\ell\ge 4(g-1)n/(5g-3)$.
* In the class of all graphs, $\ell\ge 2h+8$, equivalently $3\ell\ge 2n+8$. This last bound uses the published verification through order 40 and a separate finite calculation below.

The first three bounds also hold for a globally minimal counterexample if it has the indicated structure. Choosing a counterexample in the bipartite class allows conclusions about the first bipartite counterexample even if a smaller nonbipartite counterexample exists.

## Counting incidences across a cubic component

Every edge has an endpoint in $L$, since deleting an edge with two endpoints in $H$ preserves minimum degree three. Also each vertex of $L$ has a neighbor in $L$, since deleting a cubic vertex with only heavy neighbors preserves the degrees required at its neighbors. These deletion arguments are Lemma 3.2 in [Ducoffe and Dumitru](https://arxiv.org/html/2609.28594v1#S3).

Assume $h>0$. If $h=0$, the proportion bounds hold directly. Let $C$ be a connected component of $G[L]$. Deleting all of $C$ leaves a nonempty graph. Every remaining cubic vertex keeps all three neighbors. Minimality therefore forces at least one vertex $v\in H$ to have degree at most two after the deletion. It follows that

$$
|N(v)\cap C|\ge d_G(v)-2\ge 2.
$$

Join two such neighbors by a shortest path in $C$, of length $d$ edges. This gives a simple cycle of length $d+2$ through $v$. In particular $d\ne2$. In a triangle-free graph $d\ne1$ as well, so $|C|\ge4$. In a bipartite graph $d$ is even, hence $|C|\ge5$. A girth lower bound $g$ gives $|C|\ge g-1$.

If $C$ has $s$ vertices and $e(C)$ edges, it sends exactly $3s-2e(C)$ edges to $H$. Connectivity gives $e(C)\ge s-1$, so there are at most $s+2$ such edges. If every component has order at least $k$, summing gives

$$
4h\le\sum_{v\in H}d_G(v)\le \ell+\frac{2\ell}{k},
\qquad
\frac{\ell}{n}\ge\frac{4k}{5k+2}.
$$

The choices $k=4,5,g-1$ give the stated bounds.

## The unrestricted tradeoff with triangles

Write $c_i$ for the number of components of $G[L]$ of order $i$, and $S=\sum_{v\in H}(d_G(v)-4)$. Every component of order at least four sends at most $3s/2$ edges to $H$. Orders two and three have upper bounds four and five. The incidence count therefore gives

$$
8h+2S\le 3\ell+2c_2+c_3,
\qquad 8n+2S\le 11\ell+2c_2+c_3 .
$$

Each component counted by $c_2$ or $c_3$ contains the two light vertices of a triangle through a heavy vertex. Indeed the path constructed above has length at most two, and length two would give a four-cycle.

For a component $xy$ of order two, its common heavy neighbor $v$ has degree four. Its other two heavy incidences go to distinct vertices $a,b$, respectively, since sharing two heavy neighbors would give a four-cycle. This local description of one component was also established by [Andrew Bisch](https://ajbisch.github.io/papers/erdos-gyarfas.html). No heavy vertex can witness two components of order two. If it did, its four neighbors would all lie in these two components. The four outer heavy vertices are pairwise distinct because a repetition gives two common neighbors with $v$, creating a four-cycle. Delete $v$ and the two components. Each outer vertex loses one edge, and all other remaining vertices keep their degrees, contradicting minimality. Thus the $c_2$ triangles can be chosen vertex-disjoint.

The size-two components in particular give a stability bound. A component of size $s\ge3$ sends at most $5s/3$ edges to $H$, while a size-two component sends four. Hence $12h+3S\le 5\ell+2c_2$. Writing $E=\ell-2h=3\ell-2n$ gives

$$
3c_2\ge n-\frac{17}{2}E+\frac{9}{2}S .
$$

In particular, if the cubic fraction is at most $2/3+\varepsilon$, the vertex-disjoint triangles from the size-two components cover at least $(1-51\varepsilon/2)n$ vertices.

## Contracting disjoint triangles

**In a globally minimal counterexample, every collection of vertex-disjoint triangles leaves at least two cubic vertices uncovered.**

Take a collection of $t$ disjoint triangles. Contract each to a vertex, keeping uncovered vertices as singletons, to obtain $Q$. Two edges between blocks with distinct ends on both sides would form a 4-cycle using one edge from each triangle. If the two edges share an end, the two-edge path through the third vertex of the opposite triangle gives a 4-cycle. Thus $Q$ is simple. Each singleton keeps its degree, and each triangle has at least three distinct neighbors because every corner has an external edge. A triangle with a heavy corner has at least four.

Contract just one triangle. By minimality the smaller graph has a power-of-two cycle. It must pass through the contracted vertex and use different corners, since otherwise it would lift unchanged. Opening it at that vertex gives a path of the same power-of-two length between two triangle corners, with all internal vertices outside the triangle.

On a cycle of length $r$ in $Q$, a visit to a triangle at two different corners can use one or two internal edges. All other visits use zero internal edges. If the number $z$ of zero visits is at most $r/2$, use two edges at $z$ of the $r-z$ different-corner visits and one at the rest. This gives $r$ internal and $r$ external edges. The lift is simple because each block occurs only once. In particular, if zeros are never consecutive, the visit just after each zero can supply the extra edge. [Lean proof of the doubled cycle in this case](Erdos64/TrianglePacking.lean)

Suppose the collection misses at most one cubic vertex. It is nonempty, since $G$ has at least four cubic vertices. Indeed, a heavy vertex has at least four cubic neighbors, or every vertex is cubic. Thus $Q$ is smaller and has a power-of-two cycle by minimality. A zero visit in a triangle occurs at a corner with two external edges, which is heavy. If all uncovered vertices are heavy, every zero is heavy, so no two are consecutive. Doubling the cycle length gives the contradiction.

Suppose instead that $u$ is the unique uncovered cubic vertex. Every power-of-two cycle in $Q$ must have $z>r/2$ to escape the same lift. Since $r$ is even, it has at least $2z-r\ge2$ edges joining consecutive zeros. Each such edge must touch $u$ because heavy vertices are independent. Thus every power-of-two cycle uses $u$, and along one such cycle the two neighbors of $u$ are distinct blocks containing a heavy vertex. Both have degree at least four in $Q$.

It follows that $Q-u$ has no power-of-two cycle and has at most one degree-two vertex, since $u$ had degree three. If there is a degree-two vertex, join two copies of it in two copies of $Q-u$ by a bridge. No cycle uses the bridge. In either case we have a graph of minimum degree three on at most $2(t+h)$ vertices, where $h$ counts the uncovered heavy vertices. Their at least $4h$ incidences go to $u$ or to cubic triangle corners. Each such corner has just one external edge, so $4h\le3+3t$ and $h\le t$. The new graph has at most $2(t+h)<3t+h+1=|G|$ vertices, contradicting minimality.

**Triangle factors.** In any counterexample whose vertices can be partitioned into triangles, first delete edges between distinct triangles with two heavy ends for as long as possible. This preserves the partition and minimum degree three. The same argument applies because consecutive positions on a quotient cycle are joined by an edge between triangles. Hence contraction gives a counterexample on exactly one third as many vertices. The unrestricted bound of 42 gives a bound of **126 vertices** for a counterexample with a triangle factor. [Order bound](Order41.md)

**Cubic graphs.** A cubic counterexample with a triangle factor has at least **150 vertices**, since the quotient is cubic and a cubic counterexample has at least 50 vertices. Salehi Nowbandegani, Esfandiari, Shirdareh Haghighi and Bibak proved the cubic triangle-factor lift gives all lengths from $2r$ to $3r$ and obtained a lower bound of 114 for a cubic claw-free counterexample. [Proposition 6, Corollary 7 and Theorem 9](https://arxiv.org/pdf/1109.5398#page=5) · [Cubic order bound, Theorem 5.1](https://arxiv.org/html/2609.28594v1#S5)

A smallest cubic counterexample has at least two edges whose ends lie on no triangle. Its triangles are disjoint, since two triangles meeting at a cubic vertex would share an edge and give a 4-cycle. If there is a triangle, contract them all. The quotient is cubic, and only uncovered vertices give zero internal edges on a cycle. A power-of-two cycle in the smaller cubic graph must have more than half its vertices uncovered to escape the doubling rule. Its even length then gives at least two edges joining uncovered vertices, as above.

## An induced claw in a globally minimal counterexample

Suppose $G$ has no induced claw. In any neighborhood, two incident edges would give a 4-cycle through its center. The neighborhood is therefore a matching and isolated vertices. Its independence number is at most two, since three independent neighbors give a claw. Thus degree five or more is impossible. Every cubic vertex belongs to exactly one triangle and every heavy vertex has degree four and belongs to exactly two triangles. No triangle contains two heavy vertices.

Make a graph $K$ with one vertex for each triangle. A heavy corner joins the two triangles that share it. Each edge outside the triangles joins the triangles at its two cubic ends. Thus each triangle has three incident links, one per corner. Two shared corners between the same triangles would give a 4-cycle, as would two links at cubic corners. If two triangles shared a corner $v$ and had an external link $xy$, the path from $x$ to $v$ through the third corner of its triangle, followed by $vy$ and $yx$, would give a 4-cycle. Hence $K$ is simple and cubic. It is smaller than $G$, since each original vertex belongs to at most two triangles and each triangle has three vertices.

Orient a cycle of length $r$ in $K$. Moving between triangles uses one edge at an ordinary link and zero at a shared corner. Inside each triangle use one edge, except immediately after a shared corner, where we use a two-edge route. Its third corner is cubic and belongs to no other triangle, since the entry corner is heavy. Thus these extra vertices cannot repeat, and every shared corner used is precisely the junction of its two consecutive triangles. The resulting simple cycle has length $2r$. By minimality $K$ has a power-of-two cycle, which gives one in $G$. Hence $G$ contains an induced claw.

## Independent check of the additive bound for a globally minimal counterexample

An August 2026 preprint states the universal additive bound of eight as Theorem 1, and a bound of ten when there are at least fourteen heavy vertices as Theorem 2. The proof below independently checks its eleven-vertex calculation and uses the later order-40 result for small graphs. [*Additive Cubic-Density Constraints on Minimal Counterexamples*, Theorems 1–2](https://airaxiv.com/papers/pdf/2608.0018/?t=1786961842&v=1)

Here take $G$ minimal in the class of all graphs. Partition $L$ into $L_i$, according to the number $i=0,1,2$ of heavy neighbors. Form a graph $M$ on $H$ by representing each vertex of $L_2$ by an edge between its two heavy neighbors. Two parallel edges would lift to a four-cycle in $G$. Each simple cycle of length $r$ in $M$ lifts to a cycle of length $2r$ in $G$ by inserting its distinct representing vertices. Thus $M$ has no power-of-two cycle. A subgraph of $M$ with minimum degree at least three would give a smaller counterexample. Consequently every nonempty subgraph of $M$ has a vertex of degree at most two. This is the auxiliary graph of Lemma 3.5 in [Ducoffe and Dumitru](https://arxiv.org/html/2609.28594v1#S3.SS2).

Let $D=2h-e(M)$. Counting heavy incidences gives $|L_1|+2|L_2|=4h+S$, and $e(M)=|L_2|$. Consequently

$$
\ell-2h=D+S+|L_0|.
$$

Also $2e(G)=3\ell+4h+S$, so $\ell-2h\equiv S\pmod2$.

In a deletion order that repeatedly removes a vertex of degree at most two, the value $2|V|-|E|$ can only decrease. If $h\ge11$, retain the last eleven vertices. An eleven-vertex 2-degenerate graph without a four- or eight-cycle has at most fifteen edges, as checked below. Its deficit is at least seven. Hence $D\ge7$.

Ducoffe and Dumitru verified the conjecture for every graph of order at most 40, so $n\ge41$. Suppose $\ell-2h\le7$. Since $n=3h+(\ell-2h)$, we have $h\ge12$, hence $D\ge7$. The identity forces $\ell-2h=D=7$, $S=0$ and $|L_0|=0$. This contradicts the parity relation. [Order bound, Theorem 5.1](https://arxiv.org/html/2609.28594v1#S5)

### Reproducing the eleven-vertex check

In a reversed deletion order, each vertex attaches to at most two earlier vertices. Adding a vertex with $j$ earlier neighbors increases the deficit by $2-j$. A graph with eleven vertices and at least sixteen edges has deficit at most six throughout its construction. When the new vertex has neighbors $a,b$, it creates a four- or eight-cycle exactly when an earlier simple path of length two or six joins $a$ to $b$. The checker enumerates all ordered constructions under these rules and uses no isomorphism pruning. [Checker source](scripts/degree_suffix.cpp)

~~~sh
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror scripts/degree_suffix.cpp -o /tmp/erdos64-degree-suffix
/tmp/erdos64-degree-suffix
~~~

For orders zero through eleven, the counts are $1,1,2,8,43,277,1942,14700,107127,520851,783924,0$. This C++ check is independent of the Lean forbidden-induced-path theorems in this package.
