# Searching for an unrestricted Erdős-Gyárfás counterexample

Every graph below is finite, simple, and undirected, and a *dyadic cycle* is a simple cycle of length in $\{4, 8, 16, \ldots\}$. The unrestricted conjecture remains open. Ducoffe and Dumitru verified it exhaustively through order 40 for general graphs and order 48 for cubic graphs ([arXiv:2609.28594](https://arxiv.org/html/2609.28594v1)).

## Two exceptional vertices

Let $H$ be a connected graph with two distinct nonadjacent terminals $s, t$ of degree at least two and all other vertices of degree at least three. Assume $H$ has no dyadic cycle, and let $S$ be the set of edge lengths of simple paths between $s$ and $t$. Requiring either of the following conditions for every such graph $H$ is equivalent to the unrestricted conjecture:

1. $S$ contains $2^k$ for some $k \ge 2$.
2. $S$ contains $2^j - 1$ for some $j \ge 2$.

To derive condition 2 from the conjecture, add the edge $st$. The new graph has minimum degree three, so it contains a dyadic cycle, which must use $st$. Removing $st$ leaves a simple path of length $2^j - 1$.

To derive condition 1, identify $s$ and $t$. They have at most one common neighbor (two would form a 4-cycle in $H$), so the merged vertex has degree at least three and at most one other vertex drops to degree two. If a vertex does drop to degree two, take two disjoint copies of the quotient and join their degree-two vertices by a bridge. Every vertex now has degree at least three, and every cycle stays in one copy. By the conjecture, the quotient contains a dyadic cycle. It must pass through the merged vertex using edges that lift to opposite terminals (otherwise it already lifted to a dyadic cycle in $H$). Splitting the merged vertex opens a simple path between $s$ and $t$ of length $2^k$.

For both converses, take three disjoint copies of a connected counterexample with chosen roots $L, C, R$, introduce two new vertices $s, t$, and add the four bridge edges $Ls, sC, Ct, tR$. The only simple path from $s$ to $t$ passes through $C$ and has length two. This also shows that restricting both terminals to degree *exactly* two and requiring connectivity preserves both equivalences. Lean verifies both exact-degree-two equivalences, including the reverse construction and reduction to a connected component, in [Erdos64/Terminals.lean](Erdos64/Terminals.lean) and [Erdos64/Identification.lean](Erdos64/Identification.lean).

For a fragment $H$ of order $n$, adding $st$ keeps $n$ vertices, while identification uses $n - 1$ vertices (or $2n - 2$ when the two-copy repair is needed). The [order-41 theorem](Order41.md) therefore forces a path of length $2^j - 1$ through order 41 and both path types through order 21. When no common neighbor of $s$ and $t$ has degree three, identification needs no repair and forces a path of length $2^k$ through order 42.

## What a ring of fragments can force

For this construction, $s$ and $t$ may be adjacent. Set $a = \min S$ and $b = \max S$. Arrange $m \ge 3$ disjoint copies of $H$ in cyclic order, and at each join either identify $t_i$ with $s_{i+1}$ or add the edge $t_i s_{i+1}$. Let $j$ be the number of added edges. Each original terminal belongs to one join, and the resulting simple graph has minimum degree three.

Any simple cycle visiting more than one copy must traverse each copy from one terminal to the other. Viewing the ring as alternating copies and connectors (each connector being a single edge or an identified vertex), a cycle cannot backtrack through the same connector without repeating an edge or vertex, so it goes around the entire ring once. Conversely, any choice of paths through the $m$ copies concatenates into a simple cycle. The crossing cycle lengths are therefore exactly

$$
\bigl\{j + p_1 + \cdots + p_m : p_1, \ldots, p_m \in S\bigr\}.
$$

This yields two structural constraints on $S$:

* **Spread ($b \ge 2a + 1$).** If $b \le 2a$, use edge joins everywhere ($j = m$). Then $(b + 1)/(a + 1) < 2$, so for large enough $k$ the open interval $(2^k/(a + 1), 2^{k+1}/(b + 1))$ contains an integer $m \ge 3$. Every crossing cycle then has length strictly between $2^k$ and $2^{k+1}$. Thus the unrestricted conjecture forces $b \ge 2a + 1$. Garcia proposed the weak bound $b \ge 2a$ for cubic two-attachment fragments ([Garcia, Proposition 6.2 and discussion](https://arxiv.org/html/2609.04686v1#S6)).
* **Congruence ($\gcd$ of differences is 1).** If all lengths in $S$ agree modulo an odd prime $p$, take $m = p$ and identify every join ($j = 0$); every crossing length is divisible by $p$. If all lengths in $S$ have the same parity, take two copies, identify their starting terminals, and join their ending terminals by an edge; every crossing length has the form $1 + p_1 + p_2$, which is odd. Hence the conjecture forces the gcd of all differences between lengths in $S$ to equal 1 (taking the gcd to be 0 when $S$ is a singleton).

Each constraint alone is equivalent to the unrestricted conjecture for these fragments, since the three-copy counterexample above has $S = \{2\}$. The ring and gcd arguments here are written proofs rather than Lean formalizations.

## Identification inside a smallest counterexample

**Every edge of a smallest counterexample lies on a cycle of length $3, 5, 9, 17, \ldots$.** Take an edge $xy$ that lies in no triangle and contract it. Because $x$ and $y$ share no neighbor, every other vertex keeps its degree and the merged vertex has degree at least four. Minimality gives a dyadic cycle in the contracted graph. It must enter the merged vertex on an edge from one end of $xy$ and leave on an edge from the other (otherwise it already existed in $G$). Restoring $xy$ turns it into a cycle of length $2^k + 1$ through $xy$. In particular, a smallest counterexample has no bridge and is not bipartite. This is [Ducoffe and Dumitru, Lemma 2.1](https://arxiv.org/html/2609.28594v1#S2), formalized in [Erdos64/Identification.lean](Erdos64/Identification.lean).

The same identification argument works for any distinct $x, y$ whose common neighbors all have degree at least four: each common neighbor loses only one neighbor when $x$ and $y$ are merged, and the resulting dyadic cycle opens into a simple path of the same length between $x$ and $y$ in $G$. In particular, this applies to every pair at distance at least three ([Erdos64/Identification.lean](Erdos64/Identification.lean)).

Counting connected components induced by degree-three vertices gives $\ell \ge 2h + 8$ in a globally minimal counterexample (breaking order ties by edge count), where $\ell$ is the number of cubic vertices and $h$ is the number of vertices of degree at least four. [Zhou](https://airaxiv.com/papers/view/2608.0018/) obtained the same additive bound earlier. The proof in [DegreeComponents.md](DegreeComponents.md) uses the published order-40 check and an independent 11-vertex enumeration; the same component count gives a tradeoff between $\ell$ and disjoint triangles as well as bounds for triangle-free and bipartite counterexamples.

## A cubic graph with first dyadic cycle at 128

Let $f(6)$ be the smallest order of a cubic graph with no cycle of length $4, 8, 16, 32$, or $64$. Our construction shows **$f(6) \le 8{,}628$**, improving on Garcia's bound $f(6) \le 32{,}640$ from uniform replacements on a girth-17 base ([Garcia, Theorem 5.1](https://arxiv.org/html/2609.04686v1#S5)).

Start from a connected cubic base graph on 620 cosets in $\mathrm{PSL}(2, 31)$. Replace 84 vertices by 7-vertex pieces and 536 vertices by 15-vertex pieces, attaching the three incident edges at each replaced vertex to distinct ports (the exact choice and orientation at each vertex are given in [scripts/mixed_gadget_graph.py](scripts/mixed_gadget_graph.py)). No piece contains an internal dyadic cycle. Any simple cycle visiting both a piece and its exterior uses two of the piece's three boundary edges, so it projects to a simple base cycle and crosses each visited piece along a port-to-port path.

Each piece contributes at least three edges, counting its outgoing base edge, so any projected cycle of base length 22 or more has length at least 66. For all 100,037 simple base cycles of length at most 21, the Python verifier checks that the sum of minimum piece contributions exceeds 64. As an independent check in the expanded graph, it deletes each of the 930 connecting edges in turn and finds a shortest path between its ends; the minimum distance plus one is 65, the exact shortest length of a cycle using a connecting edge. Finally, it builds and checks a simple cycle of length 128.

~~~sh
python3 scripts/mixed_gadget_graph.py
~~~

To retrieve the labeled adjacency lists and the 128 vertices in cyclic order from this directory, run `from scripts.mixed_gadget_graph import check_construction` and `graph, cycle = check_construction()`.

## Exhaustive searches for fragments and counterexamples

Given a subcubic base graph, we can replace any subset of its vertices by triangles, attaching each incident edge to its own corner. A base cycle of length $r$ passing through $c$ replaced vertices lifts to every integer length in $[r + c, r + 2c]$, while the only other simple cycles are internal triangles. The checker [scripts/triangle_expansions.cpp](scripts/triangle_expansions.cpp) enumerates every base cycle and searches for a replacement subset whose intervals all miss every power of two from 4 upward, outputting the graph6 base and vertex mask for any survivor.

We checked two base families (including the empty replacement set) using [McKay and Piperno's nauty 2.9.3](https://pallini.di.uniroma1.it/), which emits one representative per isomorphism class:

| Connected base family | Base orders | Bases | Surviving assignments |
| --- | --- | ---: | ---: |
| All vertices cubic | 4 through 20 | 556,471 | 0 |
| Exactly two degree-two vertices, all others cubic | 4 through 18 | 1,149,185 | 0 |

Direct generation also ruled out fragments with exactly two degree-two vertices and all others cubic through order 22; the rooted search in [Bridges.md](Bridges.md) extends that bound and gives the corresponding edge-cut bounds for cubic counterexamples.

For unbounded maximum degree, it is enough to search for a smallest connected example (breaking ties by fewest edges). Because deleting an edge between two vertices of degree at least four still leaves a component of minimum degree two with at most two degree-two vertices, a smallest example has no such edge. The generator callback [scripts/geng_terminals.c](scripts/geng_terminals.c) uses this property and prunes whenever a new vertex closes a dyadic cycle. It ruled out all connected graphs through order **17** with minimum degree at least two, at most two degree-two vertices, and no dyadic cycle. A separate search in [Separators.md](Separators.md) extends this unrestricted-degree exclusion to order 24, and to order 28 with at most one degree-two vertex.

To reproduce the triangle-expansion searches from this package with nauty's `geng` on `PATH`:

~~~sh
set -eo pipefail
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror scripts/triangle_expansions.cpp -o /tmp/eg64-expand
for n in $(seq 4 2 20); do
  geng -cd3D3 "$n" | /tmp/eg64-expand
done
for n in $(seq 4 2 18); do
  m=$((3*n/2-1))
  geng -cd2D3 "$n" "$m:$m" | /tmp/eg64-expand
done
~~~

For the direct search, set `callback` to the absolute path of `scripts/geng_terminals.c` and run these commands in a built nauty 2.9.3 source tree on x86-64:

~~~sh
cc -std=c23 -O3 -Wall -Wextra -Wpedantic -Werror -mpopcnt -isystem . \
  -DMAXN=WORDSIZE -DWORDSIZE=32 -c "$callback" -o /tmp/eg64-callback.o
cc -std=gnu23 -O3 -mpopcnt -I. -DMAXN=WORDSIZE -DWORDSIZE=32 -DPRUNE=prune_terminals \
  geng.c /tmp/eg64-callback.o gtoolsW.o nautyW1.o nautilW1.o naugraphW1.o schreierW.o naurng.o \
  -o /tmp/eg64-terminals-geng
for n in $(seq 4 2 22); do
  m=$((3*n/2-1))
  /tmp/eg64-terminals-geng -cfd2D3 "$n" "$m:$m"
done
for n in $(seq 3 17); do
  /tmp/eg64-terminals-geng -cfd2 "$n"
done
~~~

The `-f` flag excludes 4-cycles, and the callback rules out the larger powers of two. These generator and C++ runs are computational exclusions over the stated families.

Allowing three degree-two vertices gives a positive control and a small classification. Among connected graphs through order 23 with exactly three degree-two vertices and all other vertices cubic, only four isomorphism classes avoid all dyadic cycles: the triangle (order 3), $H_7$ and $H'_7$ (order 7, differing in their inter-terminal distances), and $H_{15}$ (order 15). To reproduce this, rebuild the same callback with `-DMAX_TERMINALS=3` and run:

~~~sh
for n in $(seq 3 2 23); do
  m=$(((3*n-3)/2))
  /tmp/eg64-terminals-geng -cfd2D3 "$n" "$m:$m"
done
~~~

A second search in [scripts/gadget_csp.py](scripts/gadget_csp.py) gave each base vertex nine options: an unchanged vertex, a triangle, three orientations of $H_7$, the symmetric seven-vertex piece, and three orientations of $H_{15}$. No assignment avoided all dyadic cycles on any of the 621 connected cubic bases through order 14 or the 972 two-terminal bases through order 12 (up to expanded order 210, where the two-terminal run checks cycles inside each fragment). Run `python3 scripts/gadget_csp.py` with `geng` on `PATH` to replay it.
