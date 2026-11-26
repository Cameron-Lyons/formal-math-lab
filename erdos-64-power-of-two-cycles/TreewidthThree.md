# Cycles of length 4, 8, or 16 in partial 3-trees

**Theorem.** Let $H$ be a finite simple graph on at least three vertices, and let $x, y$ be distinct vertices of $H$. If every vertex except possibly $x$ and $y$ has degree at least three, and adding the edge $xy$ produces a graph of treewidth at most three, then $H$ contains a cycle of length 4, 8, or 16.

Applying this to $H = G - xy$ shows that every nonempty graph $G$ of minimum degree at least three and treewidth at most three has a 4-, 8-, or 16-cycle avoiding any prescribed edge $xy$. The bound 16 is sharp.

Call a graph *clean* if it has no cycle of length 4, 8, or 16. The proof classifies every clean piece that can grow behind a triangle of a 3-tree into six shapes.

## Pieces with three boundary vertices

Complete $H + xy$ to a 3-tree on the same vertex set (a graph built from an initial triangle by repeatedly adding a vertex adjacent to an existing triangle). We may choose the starting triangle to contain $xy$: the 4-cliques of a 3-tree form a tree of bags when each new clique attaches to an earlier bag containing its parent triangle, and the bags containing any given vertex stay connected; rooting this tree at a bag containing $xy$ and reading outward adds each vertex to the triangle shared with its parent ([Bodlaender, Theorem 35](https://cgi.di.uoa.gr/~sgk/teaching/GT/Bodlaender98-bt.pdf)). For three vertices, the completion is already a triangle.

A **piece** has three boundary vertices $a, b, c$ with no edges among them, and every interior vertex has degree at least three. Reading the tree from leaves to root, the pieces we encounter are exactly those built from three operations:

1. Start with three isolated vertices (the *empty* piece).
2. Combine two pieces by identifying their three boundary vertices in order (merging branches attached to the same triangle).
3. Introduce a new vertex $d$ inside $abc$: combine pieces on the three faces $abd, acd, bcd$, add any subset of the edges $da, db, dc$ so that $d$ has degree at least three, and keep $a, b, c$ as the boundary.

Because every triangle has a unique creator, the interiors of the combined pieces are disjoint. Every edge to an earlier vertex appears when its later endpoint is introduced, leaving only the three edges of the root triangle to be added at the end.

## Six shapes and their paths

Four of the six shapes come from graphs with three distinguished degree-two vertices called *ports*. Extending a port means attaching a new leaf to it and using that leaf as the boundary vertex in place of the old port.

* $T$ is a triangle with all three vertices as ports.
* For a three-port graph $P$ with ports $u, v, w$, form $D(P)$ from two copies of $P$ by adding the edge $u_1 u_2$ and the two-edge path $v_1 m v_2$. Its new ports are $w_1, w_2$ (the *outer* pair) and $m$ (the *middle* port).
* Set $H_7 = D(T)$, and form $H_{15} = D(H_7)$ by taking $u, v$ to be the outer pair of each copy of $H_7$.
* $H'_7$ is $K_4$ with the three edges incident to one vertex subdivided once each; the three subdivision vertices are its ports.

**Claim.** Every clean piece is empty, a three-leaf star with its leaves on the boundary, or one of $T, H_7, H'_7, H_{15}$ with some ports extended (with at least two ports of $T$ extended so the boundary stays independent).

Before any extensions, the simple path lengths between ports form contiguous integer intervals:

| Core | Outer pair | Each other pair | One length available for every pair while avoiding the third port |
| --- | --- | --- | --- |
| $T$ | 1-2 | 1-2 | 1 |
| $H_7$ | 3-6 | 2-6 | 4 |
| $H'_7$ | 2-6 | 2-6 | 4 |
| $H_{15}$ | 5-14 | 3-14 | 8 |

In $D(P)$, let $I$ be the path lengths from $u$ to $v$ and $J$ the lengths from $w$ to either $u$ or $v$, writing $I + J$ for pairwise sums. An outer-to-outer path crosses either link between the two copies, giving $J + J + \{1, 2\}$. A middle-to-outer path starts either on the target copy or on the opposite copy, giving $(1 + J) \cup (2 + I + J)$. To avoid the third port, an outer-to-outer path uses the direct edge $u_1 u_2$, while a middle-to-outer path starting on the opposite copy chooses its $v$-to-$u$ segment there to avoid $w$ (yielding $2 + 1 + 1 = 4$ in $H_7$ and $2 + 4 + 2 = 8$ in $H_{15}$). In $H'_7$, a path between two ports can go through the center (length 2), along the outer triangle (3 or 4), or through the center and out the third spoke before following the triangle (5 or 6).

All four cores are clean. A cycle crossing between the two copies in $D(P)$ uses both links and has length in $3 + I + I$, giving 5 to 7 in $H_7$ and 9 to 15 in $H_{15}$. A cycle through the center of $H'_7$ uses two subdivided spokes and one or two outer edges, giving length 5 or 6.

Extending $t$ endpoints of a port pair shifts its path lengths up by $t$. Adding an edge between any two boundary vertices of an extended or unextended core therefore closes a forbidden cycle: use an old path of length $3 - t$ in $T$ ($t \in \{1, 2\}$), length 3 when $t = 0$ and $7 - t$ otherwise in $H_7$ or $H'_7$, and length $7 - t$ in every case for $H_{15}$.

This claim implies the theorem at once. In the empty piece, root edges give each boundary vertex degree at most two. In a star, two root edges close a 4-cycle. In any of the four cores, even a single root edge closes a forbidden cycle. Every boundary vertex in a clean completion thus has degree at most two. At the root triangle containing $x$ and $y$, however, the third vertex has degree at least three in $H$, a contradiction.

## When two pieces meet

Two pieces on different faces of $abcd$ share a pair of boundary vertices, and pairing a path from each piece closes a cycle whose length is the sum of the two path lengths. When two pieces share all three boundary vertices, the same test applies whenever one of the two paths avoids the third vertex.

For the star and triangle, call a boundary pair **short** when its path lengths are $\{2\}$ (star) or $[2, 3]$ (one triangle port extended), and **long** when they are $[3, 4]$ (both triangle ports extended). Across different faces, nonempty clean pieces can coexist in only two ways:

* A star or triangle meets another star or triangle with one short pair and one long pair (two short pairs give length 4; two long pairs give 8).
* Two copies of $H_7$ meet along their outer pairs, with exactly three of the four incidences at the shared ports extended.

To verify the second bullet, check the remaining combinations. Any $H_{15}$ meets any nonempty piece to form a 16-cycle, since the minimum sum is at most $7 + 7$ and the maximum is at least $14 + 2$. A 7-vertex core forms an 8-cycle with any star or triangle by the same interval check. Two 7-vertex cores give sum interval $[m_1 + m_2 + t, 12 + t]$, where $m_i \in \{2, 3\}$ before extension and $t$ counts the extensions among the four shared incidences; missing both 8 and 16 forces $t = 3$ and $m_1 = m_2 = 3$.

### Combining pieces on the same boundary

Discard empty inputs. Whenever the omitted third vertex is a leaf in either piece, the two-face test applies to the other pair. That immediately rules out $H_{15}$ and both 7-vertex cores whenever any leaf is present: the sole exception in the two-face test has three leaves along the shared outer pair, so omitting one of those leaves lets us test a different pair (which cannot also be the outer pair). If neither piece has leaves, both are unextended 7- or 15-vertex cores; using the third-port-avoiding path in the first piece gives $4 + 4 = 8$ for two 7-vertex cores, $8 + 8 = 16$ for two 15-vertex cores, and $4 + 12 = 16$ for one of each.

Two stars close a 4-cycle. A star can combine with a triangle only when all three triangle ports are extended, and their union is $H'_7$. For two triangles, a shared unextended port gives a pair that is short on both sides with the third vertex a leaf; otherwise every pair has a leaf on at least one side, forcing exactly one short side per pair and hence three short pairs in total, impossible because each triangle has zero or two short pairs.

### Introducing a new vertex $d$

Count how many of the three faces $abd, acd, bcd$ carry nonempty pieces:

* **Zero.** All three edges from $d$ are needed to reach degree three, giving the star.
* **One**, say on $abd$. A core allows only the new edge $dc$; to give $d$ degree three, its old port must be unextended, so $dc$ simply extends that port. A star needs $dc$ and exactly one of $da, db$ (adding both gives a 4-cycle), producing a triangle with two ports extended.
* **Two**, say on $abd$ and $acd$. If both pieces are $H_7$, they meet on their outer pairs with no extra edge allowed and three shared incidences extended. Because $d$ needs degree three, exactly one incidence at $d$ is extended and both incidences at $a$ are extended. The two old outer ports on the $d$ side are thus joined by an edge and the other two by a two-edge path through $a$, producing $H_{15}$ (possibly extended at $b$ or $c$).

  Otherwise, one face has a short pair on $ad$ and the other is a triangle with a long pair on $ad$. If the short face is a triangle, no extra edge is allowed, so its $d$ port is unextended and its $a$ port is extended. If the short face is a star, $d$ has degree two and the only legal edge joins $d$ to the star's private boundary vertex, forming a triangle containing $d$. Either way we get two triangles joined by an edge on the $d$ side and a two-edge path through $a$, which is $H_7$ (possibly extended at its private ports).
* **Three.** Every pair of faces overlaps on a different edge from $d$, so the two-$H_7$ exception (which requires both copies to share their outer pairs) cannot occur across all overlaps, and all three faces are stars or triangles. In each face, pick a path between its two outside boundary vertices avoiding $d$. Together the three paths form a cycle:

| Face | Short pairs incident with $d$ | Outside path lengths avoiding $d$ |
| --- | --- | --- |
| Star | 2 | 2 |
| Triangle with $d$ unextended | 2 | 3 |
| Triangle with an outside port unextended | 1 | 2-3 |
| Triangle with all ports extended | 0 | 3-4 |

Because every shared pair has one short side and one long side, the three short-pair counts sum to 3. Counts $(1, 1, 1)$ give an 8-cycle via $2 + 3 + 3 = 8$. Counts $(2, 1, 0)$ give a first path of length 2 or 3, which completes to 8 via $2 + 2 + 4$ or $3 + 2 + 3$. This closes the induction and proves the claim.

## Exact counts and a consequence for separators

The six-shape classification is exact. The operations above realize the star, the triangle with two leaves, $H'_7$ (star plus three-leaf triangle), and $H_7$ and $H_{15}$ (two-face joins with private ports unextended), while the one-face step extends any remaining port. With an ordered boundary there are $1 + 1 + 4 + 24 + 8 + 24 = 62$ clean pieces (each factor of 24 comes from 3 choices for the middle port times 8 extension subsets). Every piece has at most 15 interior vertices, all cubic. Out of $62 \cdot 8 = 496$ possible root edge completions, exactly $8 + 4 + 60 = 72$ are clean. Among those with all three boundary degrees equal to two, the isomorphism classes are precisely $T, H_7, H'_7, H_{15}$, matching the clean three-port pieces of treewidth at most three (after completing the three ports to a triangle) studied in [RecursiveGadgets.md](RecursiveGadgets.md).

This also constrains 3-vertex separators in an unrestricted counterexample $G$. Take any 3-vertex set $S$ and any component $C$ of $G - S$. If making $S$ a clique in $G[C \cup S]$ yields treewidth at most three, root that completion at $S$ and omit the edges inside $S$. The classification applies regardless of the treewidth of $G$ as a whole: $C$ has at most 15 vertices, every vertex of $C$ is cubic in $G$, and the six shapes give every possible attachment to $S$.

## A sharp example on 34 vertices

Start from $K_4$ on vertices $A, B, C, D$. Replace $A$ and $B$ by copies of $H_{15}$ (with their middle ports facing each other along the edge $AB$) and replace $C$ by a triangle, attaching the three incident edges at each replaced vertex to distinct ports. The result is a cubic graph on $15 + 15 + 3 + 1 = 34$ vertices.

Any cycle using a connecting edge between blocks crosses each block boundary an even number of times out of three outgoing edges, so it projects to a simple cycle of $K_4$. Count each outgoing edge with the block it leaves. A cycle visiting both $H_{15}$ blocks has length at least $4 + 4 + 1 = 9$. A cycle visiting only one $H_{15}$ enters and leaves via its two outer ports and also passes through $C$ and $D$, giving length at least $6 + 2 + 1 = 9$. Each block is internally clean. Taking internal paths of lengths $6, 6, 1$ around the triangle $ABC$ plus the three connecting edges gives a 16-cycle.

To verify treewidth three, first replace $A, B, C$ by triangles on their ports. Removing $D$ leaves a 6-cycle with a triangle attached along each of three disjoint edges, which has treewidth two. Adding $D$ to every bag gives treewidth at most three. Each port triangle sits inside a bag, where we attach the width-three decomposition of $H_{15}$ rooted at its ports. Minimum degree three gives the matching lower bound of three.

## Independent certificates

Lean verifies the boundary degrees of every clean root in the finite grammar using each piece's three boundary degrees and the sets of simple path lengths up to 15 between each boundary pair (tracked separately according to whether a path visits the third boundary vertex). These data suffice because any segment of a simple crossing cycle or parent boundary path inside a piece uses two boundary endpoints (two separate segments would need four distinct boundary vertices). A crossing cycle of length at most 16 uses at most 15 edges inside any piece, and replacing its segment by a path of the same length and the same avoidance of the third vertex preserves simplicity; the same holds for recorded boundary paths. The Lean theorem `Erdos64.TreewidthProfiles.clean_root_degrees` in [Erdos64/TreewidthProfiles.lean](Erdos64/TreewidthProfiles.lean) uses `native_decide` for its finite calculations, while the graph decomposition itself is proved in prose above.

The C++ program [scripts/treewidth_three.cpp](scripts/treewidth_three.cpp) independently enumerates all piece compositions, tests label-preserving isomorphism whenever two pieces share a profile, and verifies the adjacency lists, elimination order, and 16-cycle of the 34-vertex example:

```sh
c++ -std=c++23 -O2 -Wall -Wextra -Wpedantic -Werror scripts/treewidth_three.cpp -o /tmp/eg64-treewidth-three
/tmp/eg64-treewidth-three
```

## What happens at width four

There is a 105-vertex graph of treewidth exactly four and minimum degree three whose shortest dyadic cycle has length 32. It starts from a partial 3-tree $H$ with 102 cubic vertices, one degree-four vertex, and two degree-two vertices $x, y$ at distance 16. The verifier [scripts/treewidth_four_example.py](scripts/treewidth_four_example.py) builds $H$ in 22 steps, checks a width-three elimination order, and adds the edge $xy$, leaving 104 cubic vertices and one degree-four vertex. Moving $x$ to the end of the elimination order gives width at most four. Exhaustive enumeration rules out 4-, 8-, and 16-cycles and checks a displayed 32-cycle. By the width-three theorem above, the treewidth is exactly four; this also shows why the two-exception theorem requires the treewidth bound on $H + xy$ rather than $H$ alone.

The 90-vertex graph from [RecursiveGadgets.md](RecursiveGadgets.md) has treewidth exactly five. Each of its six copies of $H_{15}$ contains a cycle passing through all three ports; deleting other internal vertices and contracting the three segments along that cycle reduces each copy to a triangle on its ports, yielding an 18-vertex minor (the triangular expansion of $K_{3,3}$). The verifier searches over subsets $S$ of eliminated vertices in this minor (where two remaining vertices are adjacent in the filled graph if and only if the minor has a path between them whose internal vertices all lie in $S$), allowing a new vertex to be eliminated only when its filled degree is at most four. Starting from the empty set, the search never reaches all 18 vertices, proving treewidth at least five. An explicit elimination order on the 90-vertex graph gives the matching upper bound of five.

```sh
python scripts/treewidth_four_example.py
```
