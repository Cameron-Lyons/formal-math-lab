# Searching for an unrestricted Erdős–Gyárfás counterexample

Throughout, graphs are finite, simple and undirected. A dyadic cycle has length in $\{4,8,16,\ldots\}$. The unrestricted conjecture remains open. Ducoffe and Dumitru report exhaustive verification through order 40 for general graphs and 48 for cubic graphs. [Primary source](https://arxiv.org/html/2609.28594v1)

## Two exceptional vertices

Consider a connected graph $H$ with distinct nonadjacent terminals $s,t$, both of degree at least two, and all other vertices of degree at least three. Assume $H$ has no dyadic cycle. Let $S$ be the set of lengths in edges of its simple $s$–$t$ paths. Each of the following statements, required of every such graph, is equivalent to the unrestricted conjecture.

1. $S$ contains $2^k$ for some $k\ge2$.
2. $S$ contains $2^j-1$ for some $j\ge2$.

For the second statement, add the edge $st$. This produces a graph of minimum degree three. Any dyadic cycle in it must use the added edge. Removing that edge gives the required path.

For the first statement, identify $s$ and $t$. Two common neighbors would form a four-cycle in $H$, so at most one neighbor is common. The identified vertex has degree at least three. At most one other vertex can fall to degree two. If this happens, take two disjoint copies of the quotient and join their deficient vertices by a bridge. Every vertex now has degree at least three and every cycle lies in one copy. In either case the conjecture gives a dyadic cycle in the quotient. It must traverse the identified vertex, entering and exiting on edges that can only lift to different terminals. Otherwise it would lift to a dyadic cycle in $H$. Splitting the identified vertex opens a simple terminal path of the same length.

For both converses, take three disjoint copies of a connected counterexample with respective roots $L,C,R$. Insert two new vertices and join the roots in the order $L$–$s$–$C$–$t$–$R$. All four new edges are bridges. The only simple $s$–$t$ path has length two. This also shows that restricting both terminals to degree *exactly* two and requiring connectedness preserves the equivalences. Lean checks both connected, exact-degree-two equivalences, including the reverse construction and passage to a connected component. [Terminal theorems](Erdos64/Terminals.lean) · [Identification lemma](Erdos64/Identification.lean)

For a fragment of order $n$, adding the edge uses $n$ vertices. Identification uses $n-1$, or $2n-2$ if the two-copy repair is needed. The order-41 theorem therefore forces the $2^j-1$ path through order 41 and both paths through order 21. When no common neighbor of the terminals has degree three, identification alone forces the $2^k$ path through order 42. [Finite bound](Order41.md)

## What a ring of fragments can force

For this construction the terminals may also be adjacent. Let $a=\min S$ and $b=\max S$. Take $m\ge3$ disjoint copies of $H$ in cyclic order. At each join either identify $t_i$ with $s_{i+1}$ or insert the edge $t_is_{i+1}$. Let $j$ count the inserted edges. Each original terminal belongs to one join, and the resulting simple graph has minimum degree three.

Any simple cycle visiting more than one copy passes from one terminal to the other in every copy. To see this, view the ring as alternating copies and connectors, where a connector is an edge or a single identified vertex. Returning through the same connector would repeat its edge or its vertex. Projecting a crossing cycle onto the cyclic order therefore traverses the whole ring exactly once. Conversely, arbitrarily chosen paths through the copies concatenate to a simple cycle. Thus the crossing lengths are exactly
$$
\bigl\{j+p_1+\cdots+p_m : p_1,\ldots,p_m\in S\bigr\}.
$$

* **Spread.** If $b\le2a$, use all edge joins. Then $(b+1)/(a+1)<2$. For sufficiently large $k$ the interval $(2^k/(a+1),2^{k+1}/(b+1))$ contains an integer $m\ge3$. Every crossing cycle lies strictly between $2^k$ and $2^{k+1}$. Therefore the unrestricted conjecture would force $b\ge2a+1$. Garcia proposed the weak inequality $b\ge2a$ for cubic two-attachment fragments. [Garcia, Proposition 6.2 and discussion](https://arxiv.org/html/2609.04686v1#S6)
* **Congruence.** If all lengths in $S$ agree modulo an odd prime $p$, use $m=p$ and identify every join. Every crossing length is divisible by $p$. If they all have the same parity, take two copies, identify their starting terminals and connect their ending terminals by an edge. Each crossing length is $1+p_1+p_2$, which is odd. Consequently the conjecture would force the gcd of the differences of the lengths in $S$ to be one, with gcd zero for a singleton.

Each restriction is itself equivalent to the unrestricted conjecture for these general fragments. A counterexample gives the connected three-copy construction above, where $S=\{2\}$. The ring and gcd arguments here are mathematical proofs in prose.

## Identification inside a smallest counterexample

**Every edge of a smallest counterexample lies on a cycle of length $3,5,9,17,\ldots$.** To see this, take an edge $xy$ outside every triangle and contract it. Its ends have no common neighbor, so every other vertex keeps its degree and the merged vertex has degree at least four. The smaller graph has a dyadic cycle by minimality. That cycle must enter the merged vertex through an edge from one end of $xy$ and leave through an edge from the other. Otherwise it already existed in $G$. Restoring $xy$ gives a cycle through this edge of length $2^k+1$. In particular a smallest counterexample has no bridge and cannot be bipartite. [Ducoffe and Dumitru, Lemma 2.1](https://arxiv.org/html/2609.28594v1#S2) · [Lean proof](Erdos64/Identification.lean)

The same operation works for any distinct $x,y$ whose common neighbors all have degree at least four. Each common neighbor loses just one neighbor under identification. The resulting dyadic cycle opens into a simple $x$–$y$ path of the same length in $G$. This applies in particular to all pairs at distance at least three. [Identification and lifting](Erdos64/Identification.lean)

Counting components induced by vertices of degree three gives $\ell\ge2h+8$ for a globally minimal counterexample, where $\ell$ is the number of cubic vertices and $h$ the number of higher-degree vertices, taking fewest edges to break order ties. Zhou previously obtained the same additive bound. The proof here uses the published order-40 check and a separate eleven-vertex enumeration. [Zhou](https://airaxiv.com/papers/view/2608.0018/) The component count also gives a tradeoff between $\ell$ and the number of disjoint triangles, and bounds for the first counterexample within the triangle-free and bipartite classes. [Proof, hypotheses and checker](DegreeComponents.md)

## A cubic graph with first dyadic cycle at 128

Write $f(6)$ for the smallest order of a cubic graph having none of the cycle lengths $4,8,16,32,64$. The construction gives **$f(6)\le8{,}628$**. Garcia obtained $f(6)\le32{,}640$ with uniform replacements on a girth-17 base. [Garcia, Theorem 5.1](https://arxiv.org/html/2609.04686v1#S5)

The base is a connected cubic graph on 620 cosets in $\mathrm{PSL}(2,31)$. Replace 84 vertices by seven-vertex pieces and 536 by fifteen-vertex pieces, attaching each of the three incident edges to a different port. The script specifies the choice and orientation at every base vertex. Each piece has no internal dyadic cycle. A simple cycle meeting a piece and its exterior uses exactly two of its three boundary edges. It therefore projects to a simple base cycle and traverses each visited piece along one port-to-port path.

Every piece contributes at least three edges, counting its outgoing base edge. A projected cycle of length 22 or more thus contributes at least 66 edges. For all 100,037 simple base cycles of lengths at most 21, the verifier checks that the sum of the minimum possible contributions exceeds 64. Independently, in the expanded graph it deletes each of the 930 connecting edges in turn and finds a shortest path between its ends. Adding one to the least of these distances gives 65, the exact length of the shortest cycle using a connecting edge. Finally it constructs and checks a simple cycle of length exactly 128. The construction and cycle checks run in Python. [Explicit design and verifier](scripts/mixed_gadget_graph.py)

~~~sh
python3 scripts/mixed_gadget_graph.py
~~~

For the labeled adjacency lists and the 128 vertices in cyclic order, use `from scripts.mixed_gadget_graph import check_construction` and `graph, cycle = check_construction()` from this directory.

## Exhaustive searches for fragments and counterexamples

For a subcubic base, replace any subset of vertices by triangles with each original incidence using its own triangle vertex. A base cycle of length $r$ that visits $c$ replacements lifts to every integer length in $[r+c,r+2c]$. The other simple cycles are internal triangles. The checker enumerates each base cycle and searches for a subset whose intervals all miss every power of two from four upwards. It outputs the base in graph6 format and the vertex mask for every surviving assignment. [C++ checker](scripts/triangle_expansions.cpp)

Two base families were checked, including the empty replacement set. The graph generator emits one representative of each isomorphism class. [McKay and Piperno's nauty 2.9.3](https://pallini.di.uniroma1.it/)

| Connected base family | Base orders | Bases | Surviving assignments |
| --- | --- | ---: | ---: |
| All vertices cubic | 4 through 20 | 556,471 | 0 |
| Exactly two degree-two vertices, all others cubic | 4 through 18 | 1,149,185 | 0 |

Direct generation ruled out a fragment with exactly two degree-two vertices and all others cubic through order 22. The independent rooted search extends this exclusion and gives corresponding order bounds for cubic counterexamples with a two-edge cut. [Rooted search and bridge bounds](Bridges.md) For a direct search with unbounded maximum degree, it suffices to look for a smallest connected example, breaking ties by the number of edges. An edge with two endpoints of degree at least four can be removed while leaving a component with minimum degree two and at most two degree-two vertices. Thus a smallest example contains no such edge. With no upper bound on degree, the search ruled out every connected graph through order **17** having minimum degree two or more, at most two degree-two vertices, and no dyadic cycle. The callback uses this observation and prunes as soon as a new vertex completes a dyadic cycle. A separate search with unrestricted maximum degree now excludes every such graph through order 24, and through 28 when there is at most one degree-two vertex. [Generator callback](scripts/geng_terminals.c) · [Extended search and separator consequences](Separators.md)

To reproduce the triangle searches, run from this package with nauty's `geng` on the path.

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

For the direct search, set `callback` to the absolute path of `scripts/geng_terminals.c`, then run the following in a built nauty 2.9.3 source tree on x86-64.

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

Here `-f` excludes four-cycles and the callback checks the remaining powers of two. The generator and C++ searches are computational exclusions over the specified families.

Allowing three degree-two vertices gives a positive control and a small classification. Among connected graphs through order 23 with exactly three vertices of degree two and every other vertex cubic, exactly four isomorphism classes avoid all dyadic cycles. Their orders are 3, 7, 7 and 15. They are the triangle, $H_7$, $H'_7$ and $H_{15}$. The two seven-vertex pieces differ in their distances between terminals. Rebuild the same callback with the additional compiler flag `-DMAX_TERMINALS=3`, then run the following with the resulting executable.

~~~sh
for n in $(seq 3 2 23); do
  m=$(((3*n-3)/2))
  /tmp/eg64-terminals-geng -cfd2D3 "$n" "$m:$m"
done
~~~

A second search gave each vertex nine choices among an unchanged vertex, a triangle, three orientations of $H_7$, a symmetric seven-vertex piece, and three orientations of $H_{15}$. No assignment avoided all dyadic cycles on any of the 621 connected cubic bases through order 14 or the 972 two-terminal bases through order 12. The largest expanded order tested was 210. The two-terminal search tested the cycles already inside each fragment. Run `python3 scripts/gadget_csp.py` with `geng` on the path. [Substitution checker](scripts/gadget_csp.py)
