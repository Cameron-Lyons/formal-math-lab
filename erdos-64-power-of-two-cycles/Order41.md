# The Erdős-Gyárfás conjecture through order 41

**Theorem.** Every nonempty finite simple graph on at most 41 vertices with minimum degree at least three contains a cycle of length 4, 8, 16, or 32. Any unrestricted counterexample therefore has at least **42 vertices**. Ducoffe and Dumitru previously verified the conjecture through order 40 ([arXiv:2609.28594, Section 5](https://arxiv.org/html/2609.28594v1#S5)).

## Proof

Suppose a counterexample on at most 41 vertices exists, and choose one, $G$, first with the fewest vertices and then with the fewest edges. Then $G$ is connected, and every edge has at least one *cubic* (degree-three) endpoint, because deleting an edge between two vertices of degree at least four preserves the hypotheses.

The search starts from a chosen induced subgraph of $G$. While some exposed vertex still needs a neighbor, we expose a fresh neighbor and branch over all possible sets of neighbors for it among the already exposed vertices. Two exposed vertices joined by an exposed simple path of length 2, 6, 14, or 30 cannot both be adjacent to the fresh vertex, because that would close a forbidden cycle. We also enforce the degree caps and reject any edge joining two vertices of degree above three. Every counterexample matches some branch of the tree until every exposed vertex has degree at least three.

To bound the maximum degree, consider a vertex of degree $d$. Its neighbors induce a matching of some $t$ edges, because two adjacent edges in the neighborhood would form a 4-cycle. Those neighbors send at least $2d - 2t$ edges outside the closed neighborhood, all to distinct vertices (again because there is no 4-cycle). Hence $1 + 3d - 2t \le 41$, which forces $d \le 20$.

The search divides all counterexamples into two cases:

1. **All triangles share a common vertex (67 cases).** If $G$ is triangle-free, pick a cubic endpoint of any edge as the center. If $G$ has triangles but no two are vertex-disjoint, all of them must meet at one vertex: two triangles sharing $v$ have disjoint pairs of other vertices, any edge between those pairs creates a 4-cycle through $v$, so any third triangle meeting both must also contain $v$. Expose the center and all of its neighbors, branch over every possible matching among those neighbors, and forbid any further triangles.
2. **Two disjoint triangles (36 distances).** Pick a pair of vertex-disjoint triangles at minimum distance $r$ and a shortest path between them. Their union is an induced subgraph (any extra edge shortens $r$ or creates a 4-cycle) on $r + 5$ vertices, so $1 \le r \le 36$. For each $r$, start from these $r + 5$ vertices and reject any branch that creates a pair of disjoint triangles at distance less than $r$. This covers all 36 distances, including adjacent triangles at $r = 1$.

Together, the 67 center cases and 36 distance cases cover every possible counterexample through order 41. All 103 searches return none.

## Reproduction

Build a 64-bit copy of [nauty 2.9.0](https://pallini.di.uniroma1.it/), then run these commands from this package directory:

```sh
NAUTY_DIR=/path/to/nauty2_9_0
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror -DUSE_NAUTY \
  -isystem "$NAUTY_DIR" scripts/root_degree_search.cpp \
  "$NAUTY_DIR/nauty.a" -o /tmp/root-degree
python3 scripts/replay_order41.py /tmp/root-degree
```

The [replay manifest](scripts/replay_order41.py) verifies every exit status and state count from the [C++ checker](scripts/root_degree_search.cpp). At each order, the checker caches canonical adjacency strings while keeping the vertex color labels needed by the search (for adjacent triangles, the connecting edge is already present, so no extra label restriction is needed). Building without nauty runs the same search uncached. For pruning, any set of exposed vertices that cannot share a fresh neighbor requires a separate fresh vertex for each of its missing incidences.

| Starting graph | Cases | Partial graphs visited |
| --- | ---: | ---: |
| Center and its neighbors | 67 | 31,203,215 |
| Adjacent disjoint triangles | 1 | 32,800,764 |
| Closest disjoint triangles at distance 2 through 36 | 35 | 24,615,340 |
| **Total** | **103** | **88,619,319** |

### A shorter replay for adjacent triangles

Passing `--split-adjacent` replaces the single adjacent-triangle run with 36 smaller searches, cutting the overall total to **65,701,105** visited states. By reflecting a smallest end block at its cut vertex, we may assume the adjacent triangles lie in the same 2-connected block (see the [end-block lemma](Separators.md#putting-adjacent-disjoint-triangles-in-one-block)). Write $ab$ for their connecting edge with $b$ cubic. Deleting $a$ leaves the block connected, and the two remaining neighbors of $b$ are adjacent, so paths can bypass $b$.

In $G - \{a, b\}$, pick a shortest path between the two remaining pairs of triangle vertices. If its length is $s$, choosing one or two edges inside each triangle produces cycles of lengths $s + 3$, $s + 4$, and $s + 5$. On these $s + 5$ vertices, only edges from $a$ to internal vertices of the path are optional; any other extra edge would shorten $s$, form a 4-cycle, or give $b$ a fourth neighbor. The checker tries every valid edge subset and rejects extensions that shorten $s$, exhausting $1 \le s \le 36$ in 9,882,550 states.

As positive controls, forbidding only 4-cycles causes the center, triangle-pair, and peripheral-path searches to return cubic graphs on 10, 12, and 12 vertices, whose adjacency rows directly check cubicity and absence of 4-cycles. An independent run for the special case of order 41 with exactly one vertex of degree above three visits 16,899,899 states; to repeat it, run the checker with `single 41 d 3 -1 700000` for each even $d$ from 4 through 20 (the only degrees allowed by parity).

## A related girth bound

If a graph of minimum degree at least three and girth at least seven has no 8-cycle, its order is at least $1 + 11D$, where $D$ is its maximum degree. Run a breadth-first search from a vertex of degree $D$. Girth at least seven ensures at least $D$, $2D$, and $4D$ vertices in layers 1, 2, and 3, each with a unique shortest path to the root. Two vertices in layer 3 have tree distance 2, 4, or 6, so they cannot share a neighbor in layer 3 or layer 4 without creating a short cycle or an 8-cycle. Layer 3 therefore has internal maximum degree at most one, leaving each vertex in layer 3 with its own private neighbor in layer 4, for another $4D$ vertices.
