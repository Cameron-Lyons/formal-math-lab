# Cycles of Length 4, 8, or 16 in Partial 3-Trees

A graph has *treewidth at most three* if it is a subgraph of a *3-tree* — a graph built from a starting triangle by repeatedly adding a new vertex adjacent to the three vertices of an existing triangle. Among structured graph families, partial 3-trees provide one of the sharpest complete results for Erdős Problem #64: every graph of treewidth at most three and minimum degree at least three contains a $4$-, $8$-, or $16$-cycle **avoiding any prescribed edge**, and a 34-vertex cubic graph proves that $16$ cannot be lowered.

**Theorem.** Let $H$ be a finite simple graph on at least three vertices, and let $x, y$ be distinct vertices of $H$. If every vertex except possibly $x$ and $y$ has degree at least three, and adding the edge $xy$ produces a graph of treewidth at most three, then $H$ contains a cycle of length **$4$, $8$, or $16$**.

Applying this theorem to $H = G - xy$ immediately yields the edge-avoidance result for every nonempty graph $G$ of minimum degree at least three and treewidth at most three. Call a graph *clean* if it has no cycle of length $4, 8,$ or $16$. The proof works bottom-up along the 3-tree, showing that every clean piece growing behind any triangle must take one of just **six shapes**.

---

## Pieces with three boundary vertices

**The big idea.** Complete $H + xy$ to a 3-tree on the same vertex set. Its $4$-cliques form a tree of bags (each new $4$-clique attaches to an earlier bag along its parent triangle, and the bags containing any fixed vertex form a connected subtree). Rooting this tree at a bag containing $xy$ and reading outward adds each remaining vertex to the triangle shared with its parent ([Bodlaender, Theorem 35](https://cgi.di.uoa.gr/~sgk/teaching/GT/Bodlaender98-bt.pdf); for three vertices, the completion is already a triangle).

Reading that same tree in reverse — from leaves back to the root triangle — builds every subgraph hanging behind a triangle from just three recursive operations. Formally, define a **piece** to be a graph with three distinguished boundary vertices $a, b, c$ having no edges among them, in which every interior vertex has degree at least three. Every piece encountered bottom-up arises from:

1. **Empty piece:** Three isolated boundary vertices $a, b, c$.
2. **Parallel merge:** Identify the three boundary vertices of two pieces in order (merging two branches attached to the same triangle).
3. **Vertex introduction:** Introduce a new interior vertex $d$ inside $abc$ — combine pieces on the three faces $abd$, $acd$, and $bcd$, add any subset of the edges $da, db, dc$ so that $d$ reaches degree at least three, and hide $d$ into the interior while keeping $a, b, c$ as the boundary.

Because every triangle in the 3-tree has a unique creator, the interiors of combined pieces are always disjoint. Every edge to an earlier vertex appears at the step where its later endpoint is introduced, leaving only the three edges of the root triangle to be added at the very end.

---

## The six clean shapes and their path lengths

Four of the six shapes are built from core graphs carrying three distinguished degree-two vertices called *ports*. **Extending a port** means attaching a new leaf edge to it and promoting that leaf to be the boundary vertex in place of the old port.

* **$T$** ($3$ vertices): a triangle with all three vertices as ports.
* **Doubling operator $D(P)$:** Given a three-port graph $P$ with ports $u, v, w$, form $D(P)$ from two disjoint copies of $P$ by adding the direct edge $u_1 u_2$ and the two-edge path $v_1 - m - v_2$. Its three new ports are $w_1, w_2$ (the *outer* pair) and $m$ (the *middle* port).
* **$H_7 = D(T)$** ($7$ vertices).
* **$H_{15} = D(H_7)$** ($15$ vertices), taking $u, v$ to be the outer pair of each copy of $H_7$.
* **$H'_7$** ($7$ vertices): $K_4$ with the three edges incident to one vertex subdivided once each; the three subdivision vertices are its ports.

**Classification Claim.** Every clean piece is one of six shapes:
1. the empty piece,
2. a three-leaf star with its leaves on the boundary, or
3. one of $T$, $H_7$, $H'_7$, or $H_{15}$ with some ports extended (with **at least two** ports of $T$ extended so that the boundary vertices remain nonadjacent).

### Port-to-port path lengths and internal cleanness

Before any port extensions, the simple path lengths between ports in all four cores form contiguous integer intervals:

| Core | Outer pair | Each other pair | One length available for every pair while avoiding the third port |
| --- | --- | --- | --- |
| $T$ | 1–2 | 1–2 | 1 |
| $H_7$ | 3–6 | 2–6 | 4 |
| $H'_7$ | 2–6 | 2–6 | 4 |
| $H_{15}$ | 5–14 | 3–14 | 8 |

Let us check both the path intervals and internal cleanness of the four cores:

* **Paths in $D(P)$:** Let $I$ be the set of simple path lengths from $u$ to $v$ in $P$, and $J$ the lengths from $w$ to either $u$ or $v$ (writing $I + J$ for pairwise sums). An outer-to-outer ($w_1$-to-$w_2$) path crosses either link between the two copies, giving $J + J + \{1, 2\}$. A middle-to-outer ($m$-to-$w_1$) path enters either copy $1$ directly or copy $2$ first before crossing $u_2 u_1$, giving $(1 + J) \cup (2 + I + J)$. To avoid the third port, an outer-to-outer path uses the direct edge $u_1 u_2$, while a middle-to-outer path starting on the opposite copy picks its $v$-to-$u$ segment avoiding $w$ (yielding $2 + 1 + 1 = 4$ in $H_7$ and $2 + 4 + 2 = 8$ in $H_{15}$).
* **Paths in $H'_7$:** Between two ports of $H'_7$, a simple path can pass straight through the center (length $2$), go around the outer triangle ($3$ or $4$), or pass through the center and out the third spoke before following the outer triangle ($5$ or $6$).
* **All four cores are clean:** Any cycle crossing between the two copies in $D(P)$ must use both links and therefore has length in $3 + I + I$, giving lengths $5$–$7$ in $H_7$ and $9$–$15$ in $H_{15}$. Any cycle through the center of $H'_7$ uses two subdivided spokes plus $1$ or $2$ outer edges, giving length $5$ or $6$.

### Why a single root edge kills every core (and proves the Theorem)

Extending $t \in \{0, 1, 2\}$ endpoints of a port pair simply shifts its path-length interval up by $t$. Adding a single direct edge between **any** two boundary vertices of an extended or unextended core therefore closes a forbidden cycle:

* **$T$** (with $t \in \{1, 2\}$ since at least two ports are extended): take an internal path of length $3 - t \in \{2, 1\}$ to close a $4$-cycle.
* **$H_7$ or $H'_7$:** take an internal path of length $3$ when $t = 0$ (closing a $4$-cycle) and length $7 - t \in \{6, 5\}$ when $t \in \{1, 2\}$ (closing an $8$-cycle).
* **$H_{15}$:** take an internal path of length $7 - t \in \{7, 6, 5\}$ for every $t \in \{0, 1, 2\}$ (closing an $8$-cycle).

**Proof of the Main Theorem from the Classification Claim.** Complete $H + xy$ to a 3-tree rooted at a triangle containing $x, y$ and a third vertex $z$, and build the clean piece behind that root triangle. In the empty piece, adding root edges gives each boundary vertex degree at most $2$. In a star, adding two root edges closes a $4$-cycle, so every boundary vertex still has degree at most $2$. In any of the four cores, even a single root edge closes a forbidden cycle, leaving every boundary vertex with degree at most $2$ (every port has degree $2$, every extended leaf has degree $1$). Thus **every** boundary vertex in a clean completion has degree at most $2$ — contradicting $\deg_H(z) \ge 3$! $\square$

---

## Proof of the classification: when two pieces meet

To prove the Classification Claim by induction over the three grammar operations, we first classify which pairs of nonempty clean pieces can coexist without closing a $4$-, $8$-, or $16$-cycle.

### The two-face compatibility test

Two pieces living on different faces of a tetrahedron $abcd$ share a pair of boundary vertices, and pairing a path from each piece closes a cycle whose length is the sum of the two path lengths. When two pieces share *all three* boundary vertices, the exact same sum test applies whenever one of the two paths avoids the third boundary vertex.

For the star and triangle, call a boundary pair **short** when its path lengths are $\{2\}$ (star) or $[2, 3]$ (triangle with one port extended), and **long** when its path lengths are $[3, 4]$ (triangle with both ports extended). Across different faces, nonempty clean pieces can coexist in **only two ways**:

1. **Short meets long:** A star or triangle meets another star or triangle with one short pair and one long pair (two short pairs sum to $4$; two long pairs sum to $8$).
2. **Double $H_7$:** Two copies of $H_7$ meet along their outer pairs, with **exactly three** of the four incidences at the shared ports extended.

**Verification of the remaining combinations:**
* Any $H_{15}$ combined with any nonempty piece closes a $16$-cycle, because the minimum sum is at most $7 + 7 = 14$ and the maximum sum is at least $14 + 2 = 16$.
* Any $7$-vertex core ($H_7$ or $H'_7$) combined with any star or triangle closes an $8$-cycle by the same interval check (minimum sum at most $5 + 3 = 8$, maximum sum at least $6 + 2 = 8$).
* Two $7$-vertex cores give sum interval $[m_1 + m_2 + t,\, 12 + t]$, where $m_i \in \{2, 3\}$ before extensions and $t \in \{0, 1, 2, 3, 4\}$ counts the extensions among the four shared incidences. Missing $8$ requires $m_1 + m_2 + t \ge 9$, while missing $16$ requires $12 + t \le 15$ (so $t \le 3$). Because $m_1 + m_2 \le 6$, this uniquely forces $t = 3$ and $m_1 = m_2 = 3$ — both outer pairs of $H_7$.

### Operation 2: Combining pieces on the same boundary

Discard empty inputs. Whenever the omitted third boundary vertex is a leaf (an extended port or a star leaf) in either piece, no simple path between the other two boundary vertices can pass through it, so the two-face compatibility test applies directly to that pair:

* **7- and 15-vertex cores with any leaf:** Immediately ruled out — the sole $7$-vertex exception in the two-face test has three leaves along the shared outer pair, so omitting one of those leaves lets us test a different boundary pair (which cannot also be the outer pair).
* **Two unextended 7- or 15-vertex cores (no leaves):** Using the third-port-avoiding path from the last column of the table in the first piece gives $4 + 4 = 8$ for two $7$-vertex cores, $8 + 8 = 16$ for two $15$-vertex cores, and $4 + 12 = 16$ for one of each.
* **Stars and triangles:** Two stars close a $4$-cycle. A star can combine with a triangle only when all three triangle ports are extended (so every pair is short + long), and their union is **$H'_7$**. Finally, two triangles can never combine cleanly: if they share an unextended port, the two pairs incident to it are short on both sides while the third vertex is a leaf; otherwise every pair has a leaf on at least one side, forcing exactly one short side per pair and hence $3$ short pairs in total — impossible, because each triangle has either $0$ or $2$ short pairs (an even number!).

### Operation 3: Introducing a new vertex $d$

Count how many of the three faces $abd, acd, bcd$ carry nonempty pieces:

* **Zero nonempty faces:** All three edges $da, db, dc$ are required for $d$ to reach degree three, producing the **star**.
* **One nonempty face** (say on $abd$):
  * If the piece on $abd$ is a core, neither $da$ nor $db$ is allowed (a single root edge kills every core), so only $dc$ can be added. For $d$ to reach degree three, its old port must be unextended (degree $2$), so adding $dc$ simply **extends that port** to $c$.
  * If the piece on $abd$ is a star, $d$ needs $dc$ plus *exactly one* of $da, db$ (adding both closes a $4$-cycle), producing a **triangle with two ports extended**.
* **Two nonempty faces** (say on $abd$ and $acd$, overlapping on $ad$):
  * **Both pieces are $H_7$:** By the two-face test, they meet along their outer pairs with no extra edge allowed and $3$ of the $4$ shared incidences extended. Because $d$ needs degree at least three, at least one of its two incidences must be unextended (degree $2$), which forces *exactly one* incidence at $d$ extended and *both* incidences at $a$ extended. Thus the two old outer ports on the $d$-side are joined by a single edge (through $d$, which has degree $3$) and the two on the $a$-side are joined by a two-edge path through $a$ — which is **$H_{15}$** (possibly extended at $b$ or $c$)!
  * **Stars/triangles (one short on $ad$, one triangle long on $ad$):** If the short face is a triangle, no extra edge is allowed, so its $d$-port is unextended and its $a$-port is extended. If the short face is a star, $d$ has degree $2$ and the only legal extra edge joins $d$ to the star's private boundary vertex (forming a triangle containing $d$). Either way, we get two triangles joined by a single edge on the $d$-side and a two-edge path through $a$ — which is **$H_7$** (possibly extended at its private ports)!
* **Three nonempty faces:** Every pair of faces overlaps along a different edge from $d$, so the two-$H_7$ exception (requiring both copies to share their unique outer pair) cannot occur across all three overlaps. Hence all three faces are stars or triangles. Inside each face, pick a simple path between its two outside boundary vertices avoiding $d$; together the three paths form a cycle on $a, b, c$:

| Face | Short pairs incident with $d$ | Outside path lengths avoiding $d$ |
| --- | --- | --- |
| Star | 2 | 2 |
| Triangle with $d$ unextended | 2 | 3 |
| Triangle with an outside port unextended | 1 | 2–3 |
| Triangle with all ports extended | 0 | 3–4 |

Because each of the three shared pairs $ad, bd, cd$ has one short side and one long side, the three short-pair counts must sum to $3$. Up to permutation, the only partitions are:
  * **$(1, 1, 1)$:** Gives an $8$-cycle via $2 + 3 + 3 = 8$.
  * **$(2, 1, 0)$:** The first face gives path length $2$ or $3$, which completes to an $8$-cycle via $2 + 2 + 4 = 8$ or $3 + 2 + 3 = 8$.

This closes the induction and proves the Classification Claim. $\square$

---

## Exact counts and a consequence for separators

The six-shape classification is exact — every single allowed shape actually occurs:

* The operations above realize the star, the triangle with two leaves, $H'_7$ (star plus three-leaf triangle), and $H_7$ and $H_{15}$ (two-face joins with private ports unextended), while the one-face step extends any remaining port.
* With an ordered boundary $(a, b, c)$, there are **$1 + 1 + 4 + 24 + 8 + 24 = 62$** clean pieces (each factor of $24$ comes from $3$ choices for the middle port times $2^3 = 8$ extension subsets). Every clean piece has at most $15$ interior vertices, all cubic.
* Out of $62 \cdot 8 = 496$ possible root-triangle edge completions, exactly **$8 + 4 + 60 = 72$** are clean. Among those where all three boundary vertices have degree two, the isomorphism classes are precisely $T, H_7, H'_7, H_{15}$ — matching the clean three-port pieces of treewidth at most three (after completing the three ports to a triangle) studied in [RecursiveGadgets.md](RecursiveGadgets.md).

### Local constraint on 3-vertex separators

This classification also constrains $3$-vertex separators inside an **unrestricted** counterexample $G$ of arbitrarily high treewidth. Take any $3$-vertex set $S$ and any component $C$ of $G - S$. If turning $S$ into a triangle inside $G[C \cup S]$ yields a graph of treewidth at most three, root that completion at $S$ and omit the edges inside $S$. The classification applies locally regardless of the treewidth of $G$ as a whole: **$C$ has at most $15$ vertices, every vertex of $C$ is cubic in $G$, and the six shapes describe every possible attachment of $C$ to $S$**.

---

## A sharp example on 34 vertices

Start from $K_4$ on vertices $A, B, C, D$. Replace $A$ and $B$ by copies of $H_{15}$ (with their middle ports facing each other across the edge $AB$) and replace $C$ by a triangle $T$, attaching the three incident edges at each replaced vertex to its three distinct ports. The resulting cubic graph has $15 + 15 + 3 + 1 = \mathbf{34}$ vertices.

* **No 4- or 8-cycle, and an explicit 16-cycle:** Each block is internally clean. Any cycle using a connecting edge crosses each block boundary an even number of times (hence twice out of three outgoing edges), so it projects to a simple cycle of $K_4$. Counting each outgoing edge with the block it leaves:
  * A cycle visiting both $H_{15}$ blocks has length at least $4 + 4 + 1 = 9$.
  * A cycle visiting only one $H_{15}$ block enters and leaves through its two outer ports (avoiding $AB$, hence using the edge between $A$ or $B$ and $C, D$) and also passes through $C$ and $D$, giving length at least $6 + 2 + 1 = 9$.
  * Taking internal paths of lengths $6, 6, 1$ around the triangle $ABC$ plus the $3$ connecting edges gives a $16$-cycle ($6 + 6 + 1 + 3 = 16$).
* **Treewidth is exactly three:** First replace $A, B, C$ by triangles on their ports. Removing $D$ leaves a $6$-cycle with a triangle attached along each of three disjoint edges, which has treewidth $2$; adding $D$ to every bag gives treewidth at most $3$. Each port triangle sits inside a bag, where we attach the width-$3$ decomposition of $H_{15}$ rooted at its ports. Minimum degree three supplies the matching lower bound $\operatorname{tw} \ge 3$.

---

## Independent certificates

* **Lean profile check:** Lean verifies the boundary degrees of every clean root in the finite grammar using each piece's three boundary degrees and the sets of simple path lengths up to $15$ between each boundary pair (tracked separately according to whether a path visits the third boundary vertex). These data are exact: any segment of a simple crossing cycle or parent boundary path inside a piece uses two boundary endpoints (two separate segments would require four distinct boundary vertices); a crossing cycle of length at most $16$ uses at most $15$ edges inside any piece; and swapping a segment for a path of the same length and same third-vertex avoidance preserves simplicity (and likewise for recorded boundary paths). The Lean theorem `Erdos64.TreewidthProfiles.clean_root_degrees` in [Erdos64/TreewidthProfiles.lean](Erdos64/TreewidthProfiles.lean) uses `native_decide` for its finite calculations, while the 3-tree graph decomposition itself is proved in prose above.
* **C++ independent verifier:** The program [scripts/treewidth_three.cpp](scripts/treewidth_three.cpp) independently enumerates all piece compositions, tests label-preserving graph isomorphism whenever two pieces share a profile, and verifies the adjacency lists, elimination order, and $16$-cycle of the 34-vertex example:

```sh
c++ -std=c++23 -O2 -Wall -Wextra -Wpedantic -Werror scripts/treewidth_three.cpp -o /tmp/eg64-treewidth-three
/tmp/eg64-treewidth-three
```

---

## What happens at width four and five

* **Treewidth four (105 vertices, shortest dyadic cycle 32):** There is a $105$-vertex graph of treewidth **exactly four** and minimum degree three whose shortest dyadic cycle has length $32$. It begins with a partial 3-tree $H$ having $102$ cubic vertices, one degree-four vertex, and two degree-two vertices $x, y$ at distance $16$. The verifier [scripts/treewidth_four_example.py](scripts/treewidth_four_example.py) builds $H$ in $22$ steps, checks a width-three elimination order for $H$, and then adds the single edge $xy$ (leaving $104$ cubic vertices and one degree-four vertex). Moving $x$ to the end of the elimination order gives treewidth at most $4$. Exhaustive enumeration rules out $4$-, $8$-, and $16$-cycles and checks an explicit $32$-cycle. By the width-three theorem above, the treewidth is **exactly four** — which also demonstrates why our two-exception theorem requires the treewidth bound on $H + xy$ rather than on $H$ alone.
* **Treewidth five (the 90-vertex graph from [RecursiveGadgets.md](RecursiveGadgets.md)):** The $90$-vertex cubic graph built by placing $H_{15}$ on the $6$ vertices of $K_{3,3}$ has treewidth **exactly five**. Each copy of $H_{15}$ contains a cycle passing through all three ports; deleting other internal vertices and contracting the three segments along that cycle reduces each copy to a triangle on its ports, yielding an $18$-vertex minor (the triangular expansion of $K_{3,3}$). The verifier searches over subsets $S$ of eliminated vertices in this minor (where two remaining vertices are adjacent in the filled graph if and only if the minor has a path between them whose internal vertices all lie in $S$), allowing a new vertex to be eliminated only when its filled degree is at most $4$. Starting from $\emptyset$, the search never reaches all $18$ vertices, proving treewidth at least $5$. An explicit elimination order on the $90$-vertex graph provides the matching upper bound of $5$.

```sh
python scripts/treewidth_four_example.py
```
