# The Erdős–Gyárfás conjecture through order 41

**Theorem.** Every nonempty finite simple graph on at most 41 vertices with minimum degree at least three contains a cycle of length 4, 8, 16 or 32. Thus an unrestricted counterexample has at least **42 vertices**. Ducoffe and Dumitru verified the conjecture through order 40. [Previous bound, Section 5](https://arxiv.org/html/2609.28594v1#S5)

## Proof

Suppose otherwise. Choose a counterexample $G$ with the fewest vertices and then the fewest edges. It is connected. Each edge has a cubic endpoint, since deleting an edge between two vertices of degree at least four preserves the hypotheses. Here *cubic* means degree three.

The computation starts from an induced subgraph. As long as an exposed vertex still needs a neighbor, expose a fresh neighbor and try all its possible neighbors among the old vertices. Two old vertices joined by a simple path of length 2, 6, 14 or 30 cannot both be chosen, since that would close a forbidden cycle. Enforce the degree bounds and reject adjacent vertices of degree above three. Every counterexample supplies one of the branches until all exposed degrees reach three.

A vertex of degree $d$ has a matching of $t$ edges among its neighbors, since two incident edges there would give a 4-cycle. The neighbors send at least $2d-2t$ edges outside the closed neighborhood, all to different vertices, again by the absence of a 4-cycle. Hence $1+3d-2t\le41$ and $d\le20$.

1. **Triangles with a common vertex.** If there are no triangles, take a cubic endpoint of any edge as the center. If there are triangles but no disjoint pair, they all meet at one vertex. Indeed, two distinct triangles sharing a vertex $v$ have disjoint pairs of other vertices. An edge between those pairs gives a 4-cycle through $v$. A triangle meeting both must therefore contain $v$. Expose the center and all its neighbors, try every possible matching among them, and forbid additional triangles. The search exhausts these cases.
2. **Two disjoint triangles.** Choose a pair at minimum distance $r$ and take a shortest joining path. Their union is induced, since any extra edge would shorten the distance or create a 4-cycle. It has $r+5$ vertices, so $1\le r\le36$. For each $r$ start with precisely these two triangles and their path. Reject a branch whenever it exhibits disjoint triangles closer than $r$. This exhausts all 36 distances, including adjacent triangles at $r=1$.

The 67 center cases and 36 distances cover every counterexample. All 103 searches returned none.

## Reproduction

Use a configured nauty 2.9.0 build with 64-bit words. Run these commands from the package directory. [nauty distribution](https://pallini.di.uniroma1.it/)

```sh
NAUTY_DIR=/path/to/nauty2_9_0
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror -DUSE_NAUTY \
  -isystem "$NAUTY_DIR" scripts/root_degree_search.cpp \
  "$NAUTY_DIR/nauty.a" -o /tmp/root-degree
python3 scripts/replay_order41.py /tmp/root-degree
```

The manifest checks every exit status and the state total for each group. The checker caches canonical adjacency strings separately at each order, preserving the vertex labels required by the search. For adjacent triangles, the connecting edge is already present and no further label restriction is needed. A build without nauty performs the same search without caching. To prune a branch, any set of vertices that cannot share a fresh neighbor needs a distinct fresh vertex for each of its missing incidences. [Checker](scripts/root_degree_search.cpp) · [Replay manifest](scripts/replay_order41.py)

| Starting graph | Cases | Partial graphs visited |
| --- | ---: | ---: |
| Center and its neighbors | 67 | 31,203,215 |
| Adjacent disjoint triangles | 1 | 32,800,764 |
| Closest disjoint triangles at distance 2 through 36 | 35 | 24,615,340 |
| **Total** | **103** | **88,619,319** |

### A shorter replay for adjacent triangles

Passing `--split-adjacent` replaces the single adjacent-triangle run with 36 smaller searches, giving **65,701,105** visits overall. By reflecting a smallest end block at its cut vertex, we may assume the adjacent triangles lie in one 2-connected block. Write $ab$ for their joining edge with $b$ cubic. Deleting $a$ leaves the block connected. The two neighbors left at $b$ are adjacent, so paths can bypass $b$. [End-block lemma](Separators.md#putting-adjacent-disjoint-triangles-in-one-block)

In $G-\{a,b\}$ choose a shortest path between the two remaining pairs of triangle vertices. Its length $s$ gives cycles of lengths $s+3,s+4,s+5$ by taking one or two edges in each triangle. On these $s+5$ vertices only edges from $a$ to the path interior are optional. Any other extra edge shortens the path, creates a 4-cycle, or gives $b$ a fourth neighbor. The checker tries every allowed choice and discards extensions that shorten $s$. It exhausts $1\le s\le36$ in 9,882,550 states.

With 4 as the sole forbidden length, the center, triangle-pair and peripheral-path searches return cubic graphs on 10, 12 and 12 vertices, respectively. Their adjacency rows independently verify cubicity and absence of 4-cycles. An independent calculation for the special case of order 41 with a single vertex above degree three took 16,899,899 states. To repeat it, run the checker with `single 41 d 3 -1 700000` for each even $d$ from 4 through 20, the only possible exceptional degrees by parity.

## A related girth bound

If a graph of minimum degree at least three and girth at least seven has no 8-cycle, its order is at least $1+11D$, where $D$ is its maximum degree. In breadth-first search from a vertex of degree $D$, girth gives at least $D,2D,4D$ vertices in the first three layers and unique shortest paths to the root. Two third-layer vertices cannot share a neighbor in layer three or four, since their tree distance is two, four or six. Thus the third layer has internal maximum degree one, and each of its vertices has its own neighbor in the fourth layer. This gives another $4D$ vertices.
