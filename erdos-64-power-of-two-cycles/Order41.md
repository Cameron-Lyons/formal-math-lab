# The Erdős–Gyárfás Conjecture Through Order 41

Could a counterexample to Erdős Problem #64 hide on $41$ or fewer vertices? No. By combining a short structural case split with a reproducible C++ search backed by nauty, we exhaust every possible configuration on at most $41$ vertices and push the minimum order of an unrestricted counterexample to **42 vertices**.

**Theorem.** Every nonempty finite simple graph on at most $41$ vertices with minimum degree at least three contains a cycle of length $4, 8, 16,$ or $32$. Any unrestricted counterexample therefore has at least **42 vertices**.

Ducoffe and Dumitru previously verified the conjecture through order $40$ ([arXiv:2609.28594, Section 5](https://arxiv.org/html/2609.28594v1#S5)).

---

## Proof

**Strategy.** Rather than blindly generating all graphs up to $41$ vertices, we pick a *minimal* counterexample and pin down a clean, rigid starting seed inside it. Either all triangles meet at a single center vertex (67 possible local neighborhoods), or there are two vertex-disjoint triangles connected by a shortest path of length $r \in \{1, \ldots, 36\}$ (36 induced seeds). From each of these $103$ seeds, a vertex-exposing search branches on every legal completion up to $41$ vertices and verifies that none survives.

### Step 1: Minimality and the search engine

Suppose a counterexample on at most $41$ vertices exists, and choose one, $G$, first with the fewest vertices and then with the fewest edges. Then $G$ is connected, and every edge has at least one *cubic* (degree-three) endpoint — deleting an edge between two vertices of degree at least four would preserve minimum degree three and strictly reduce the edge count.

Each search starts from a chosen induced subgraph of $G$ and grows an *exposed* induced subgraph one vertex at a time:

* While some exposed vertex still needs another neighbor, we introduce a *fresh* vertex adjacent to it and branch over all subsets of already-exposed vertices that could form the fresh vertex's neighborhood.
* Two exposed vertices already joined by an exposed simple path of length $2, 6, 14,$ or $30$ cannot both be adjacent to the fresh vertex, because that would immediately close a forbidden cycle of length $4, 8, 16,$ or $32$.
* We enforce the degree caps and reject any edge joining two vertices of degree above three.

Every counterexample matches some branch of the search tree until every exposed vertex reaches degree at least three.

### Step 2: Bounding the maximum degree ($d \le 20$)

Consider any vertex $v$ of degree $d$ in $G$. Its neighborhood $N(v)$ induces a matching of some $t$ edges ($0 \le 2t \le d$), because two adjacent edges inside $N(v)$ would form a $4$-cycle through $v$. Count edges leaving the closed neighborhood $N[v] = \{v\} \cup N(v)$:

* Each of the $2t$ matched neighbors already has $v$ and its partner in $N(v)$, so minimum degree three gives it at least $1$ edge leaving $N[v]$.
* Each of the $d - 2t$ unmatched neighbors has only $v$ inside $N[v]$, so it has at least $2$ edges leaving $N[v]$.

That yields at least $2t \cdot 1 + (d - 2t) \cdot 2 = 2d - 2t$ edges exiting $N[v]$. All of their outside endpoints must be **distinct** — two neighbors of $v$ sharing a common outside neighbor would close a $4$-cycle with $v$. Counting $v$, $N(v)$, and these outside vertices gives

$$
1 + d + (2d - 2t) = 1 + 3d - 2t \le 41.
$$

Because $2t \le d$, we have $1 + 2d \le 1 + 3d - 2t \le 41$, which forces **$d \le 20$**.

### Step 3: Exhaustive split into 103 starting configurations

Every counterexample on at most $41$ vertices falls into one of two cases:

1. **All triangles share a common vertex (67 cases):**
   * If $G$ is triangle-free, pick a cubic endpoint of any edge as the center ($d = 3, t = 0$: $1$ case).
   * If $G$ contains triangles but no two of them are vertex-disjoint, then **all triangles must meet at a single vertex**: two triangles sharing a vertex $v$ have disjoint pairs of opposite corners, and any edge between those two pairs would create a $4$-cycle through $v$, so any third triangle intersecting both triangles must also pass through $v$.

   Expose the center $v$ and all $d \le 20$ of its neighbors, branch over every possible matching size $t$ compatible with $1 + 3d - 2t \le 41$ ($66$ cases with $t \ge 1$, plus the triangle-free cubic center $= 67$ cases total), and forbid any further triangles outside $N[v]$.

2. **Two vertex-disjoint triangles (36 distances):**
   Pick a pair of vertex-disjoint triangles at minimum distance $r$ and a shortest path between them. Their union is an **induced** subgraph of $G$ (any extra edge would either shorten the minimum distance $r$ or close a $4$-cycle) on $3 + 3 + (r - 1) = r + 5$ vertices, so $1 \le r \le 36$. For each $r$, start from these $r + 5$ vertices and reject any branch that creates a pair of disjoint triangles at distance strictly less than $r$. This covers all $36$ distances, including adjacent triangles at $r = 1$.

Together, the $67$ center cases and $36$ distance cases cover every possible counterexample through order $41$. All **103** searches return none. $\square$

---

## Reproduction

Build a 64-bit copy of [nauty 2.9.0](https://pallini.di.uniroma1.it/), then run these commands from this package directory:

```sh
NAUTY_DIR=/path/to/nauty2_9_0
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror -DUSE_NAUTY \
  -isystem "$NAUTY_DIR" scripts/root_degree_search.cpp \
  "$NAUTY_DIR/nauty.a" -o /tmp/root-degree
python3 scripts/replay_order41.py /tmp/root-degree
```

The [replay manifest](scripts/replay_order41.py) verifies every exit status and state count produced by the [C++ checker](scripts/root_degree_search.cpp). At each order, the checker caches canonical adjacency strings while preserving the vertex color labels required by the search (for adjacent triangles, the connecting edge is already present, so no extra label restriction is needed). Building without nauty runs the exact same search uncached. For pruning, any set of exposed vertices that cannot share a fresh neighbor requires a separate fresh vertex for each of its missing incidences.

| Starting graph | Cases | Partial graphs visited |
| --- | ---: | ---: |
| Center and its neighbors | 67 | 31,203,215 |
| Adjacent disjoint triangles | 1 | 32,800,764 |
| Closest disjoint triangles at distance 2 through 36 | 35 | 24,615,340 |
| **Total** | **103** | **88,619,319** |

### A shorter replay for adjacent triangles

Passing `--split-adjacent` replaces the single adjacent-triangle run ($32{,}800{,}764$ states) with $36$ smaller searches, cutting the overall total to **65,701,105** visited states.

Why is this split sound? By reflecting a smallest end block across its cut vertex, we may assume that any pair of adjacent disjoint triangles lies inside the same $2$-connected block (see the [end-block lemma](Separators.md#putting-adjacent-disjoint-triangles-in-one-block)). Write $ab$ for their connecting edge, with $b$ cubic (since every edge has a cubic endpoint). Deleting $a$ leaves the block connected, and the two remaining neighbors of $b$ are adjacent (they are the other two corners of $b$'s triangle), so any path through $b$ can bypass $b$ directly along that triangle edge.

Thus, in $G - \{a, b\}$, there is still a path joining the remaining pair of corners of $a$'s triangle to the remaining pair of corners of $b$'s triangle. Pick a shortest such path, say of length $s$:

* Walking along $ab$, choosing $1$ or $2$ internal edges inside each triangle, and traversing the path of length $s$ produces cycles of lengths $s + 3$, $s + 4$, and $s + 5$ (so $s$ cannot allow any of these to be a power of two).
* On these $s + 5$ vertices, **only edges from $a$ to internal vertices of the path are optional**; any other extra edge would shorten $s$, form a $4$-cycle, or give the cubic vertex $b$ a fourth neighbor.

The checker tries every valid subset of optional edges from $a$ and rejects extensions that shorten $s$, exhausting all $1 \le s \le 36$ in **9,882,550** states.

### Positive controls and single-heavy-vertex check

* **Positive controls:** When forbidding only $4$-cycles, the center, triangle-pair, and peripheral-path searches return cubic graphs on $10$, $12$, and $12$ vertices, whose adjacency rows directly verify cubicity and the absence of $4$-cycles.
* **Single heavy vertex at order 41:** An independent run for the special case of order $41$ with exactly one vertex of degree above three visits **16,899,899** states. To repeat it, run the checker with `single 41 d 3 -1 700000` for each even $d$ from $4$ through $20$ (parity forces the unique heavy degree $d$ to be even on $41$ vertices).

---

## A related girth bound

**Proposition.** If a finite simple graph of minimum degree at least three and girth at least seven has no $8$-cycle, then its order is at least $1 + 11D$, where $D$ is its maximum degree.

**Proof.** Run a breadth-first search (BFS) starting from a vertex $v$ of degree $D$:

* **Layers 0 through 3:** Because the graph has girth at least $7$ (no cycles of length $\le 6$), no edges appear inside layers $1$ or $2$, and no two vertices in layers $1$ or $2$ share a child in the next layer. Every vertex has degree at least $3$, so layers $0, 1, 2,$ and $3$ contain at least $1$, $D$, $2D$, and $4D$ vertices, respectively, each with a unique shortest path back to $v$.
* **Layer 3 to layer 4:** Any two vertices in layer $3$ sit at distance $2, 4,$ or $6$ in the BFS tree. If two layer-$3$ vertices shared a common neighbor in layer $3$ or layer $4$, that neighbor would close a simple cycle of length $4, 6,$ or $8$ — all forbidden! Consequently:
  1. No vertex in layer $3$ can have two neighbors in layer $3$ (those two neighbors would share it), so layer $3$ has internal maximum degree at most $1$.
  2. Each vertex in layer $3$ has degree at least $3$, one parent in layer $2$, and at most one neighbor in layer $3$, leaving at least one neighbor in layer $4$ — and all of these layer-$4$ neighbors are pairwise distinct!

That yields at least $4D$ additional vertices in layer $4$, for a total of at least $1 + D + 2D + 4D + 4D = 1 + 11D$ vertices. $\square$
