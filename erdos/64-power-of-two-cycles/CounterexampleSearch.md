# Searching for an Unrestricted Erdős–Gyárfás Counterexample

Every graph below is finite, simple, and undirected, and a *dyadic cycle* is a simple cycle of length in $\{4, 8, 16, \ldots\}$. The unrestricted Erdős–Gyárfás conjecture remains open: Ducoffe and Dumitru verified it exhaustively through order $40$ for general graphs and order $48$ for cubic graphs ([arXiv:2609.28594](https://arxiv.org/html/2609.28594v1)), and [Order41.md](Order41.md) extends the general bound to order $41$.

This document approaches the conjecture from two complementary directions:

1. **Exact reformulations and local structure:** Translating the full conjecture into path-length constraints between two boundary *terminals* of a smaller fragment, gluing fragments into rings to force spread and congruence laws, and recording contraction properties of a smallest counterexample.
2. **Constructions and computational searches:** Building an **8,628-vertex** cubic graph whose shortest dyadic cycle has length $128$, and running exhaustive searches over triangle expansions, bounded-terminal fragments, and multi-gadget replacements.

---

## Two exceptional vertices: exact equivalences

Instead of looking for a closed counterexample all at once, we can cut a graph open at two vertices and ask what simple path lengths *must* exist between them.

Let $H$ be a connected graph with two distinct nonadjacent *terminals* $s, t$ of degree at least two and all other vertices of degree at least three. Assume $H$ has no dyadic cycle, and let $S$ be the set of edge lengths of all simple paths between $s$ and $t$ in $H$. Requiring **either** of the following conditions across all such fragments $H$ is equivalent to the full unrestricted conjecture:

1. **Power-of-two path:** $S$ contains $2^k$ for some $k \ge 2$.
2. **One-less-than-power-of-two path:** $S$ contains $2^j - 1$ for some $j \ge 2$.

### Why the conjecture implies both conditions

* **Condition 2 ($2^j - 1 \in S$):** Add the edge $st$ to $H$. Every vertex now has degree at least three, so the conjecture produces a dyadic cycle. Since $H$ itself had none, that cycle must use the new edge $st$; deleting $st$ leaves a simple $s$-$t$ path of length $2^j - 1$.
* **Condition 1 ($2^k \in S$):** Merge (identify) $s$ and $t$ into a single vertex $w$. Because $s$ and $t$ have at most one common neighbor (two would form a $4$-cycle in $H$), the merged vertex $w$ has degree at least $2 + 2 - 1 = 3$, and at most one other vertex (their unique common neighbor, if it had degree three) drops to degree two. If a vertex does drop to degree two, take two disjoint copies of the quotient and join their degree-two vertices by a bridge. Every vertex now has degree at least three and every cycle stays inside one copy, so the conjecture gives a dyadic cycle in the quotient. That cycle must pass through $w$ entering on an edge from one terminal and leaving on an edge from the other (otherwise it already lifted to a dyadic cycle in $H$). Splitting $w$ back into $s$ and $t$ opens it into a simple $s$-$t$ path of length $2^k$.

### Why either condition implies the conjecture

Suppose a connected counterexample $G$ existed. Take three disjoint copies of $G$ with chosen root vertices $L, C, R$, introduce two new vertices $s$ and $t$, and add the four bridge edges $Ls, sC, Ct, tR$. Every vertex except $s$ and $t$ has degree at least three, $s$ and $t$ are nonadjacent of degree exactly two, and no cycle can cross a bridge, so the combined graph has no dyadic cycle. Yet the *only* simple path between $s$ and $t$ passes through $C$ and has length $2$, so $S = \{2\}$ — violating both Condition 1 and Condition 2!

Notice that this reverse construction also proves that restricting both terminals to degree *exactly* two and requiring connectivity preserves both equivalences. Lean verifies both exact-degree-two equivalences — including the reverse construction and reduction to a connected component — in [Erdos64/Terminals.lean](Erdos64/Terminals.lean) and [Erdos64/Identification.lean](Erdos64/Identification.lean).

### Finite-order consequences

For a fragment $H$ of order $n$:
* Adding the edge $st$ keeps $n$ vertices.
* Identifying $s$ and $t$ uses $n - 1$ vertices (or $2n - 2$ vertices when the two-copy bridge repair is needed).

Combining these sizes with the [order-41 theorem](Order41.md) forces a path of length $2^j - 1$ for every such fragment through order $41$, and forces **both** path types through order $21$. When no common neighbor of $s$ and $t$ has degree three, identification needs no repair and forces a path of length $2^k$ through order $42$.

---

## What a ring of fragments can force

**The big idea.** String $m$ identical copies of a fragment $H$ into a necklace. Any cycle wrapping around the necklace picks one $s$-$t$ path from each copy, so the crossing cycle lengths are $m$-fold sums from $S$ (plus one for each connector edge). If the set $S$ is either too narrow or misses a residue class modulo some prime, we can tune the ring size $m$ so that every crossing cycle dodges every power of two.

For this construction, $s$ and $t$ are allowed to be adjacent. Set $a = \min S$ and $b = \max S$. Arrange $m \ge 3$ disjoint copies of $H$ in cyclic order, and at each join from copy $i$ to copy $i + 1$ (indices mod $m$), either identify $t_i$ with $s_{i+1}$ or add a single connecting edge $t_i s_{i+1}$. Let $j$ be the number of added connecting edges. Each original terminal participates in one join, so the resulting simple graph has minimum degree at least three.

Any simple cycle visiting more than one copy must traverse each visited copy from one terminal to the other. Viewing the ring as alternating copies and connectors (each connector being a single edge or an identified vertex), a simple cycle cannot double back through the same connector without repeating a vertex or edge, so it must wrap around the entire ring exactly once. Conversely, any choice of paths $p_1, \ldots, p_m \in S$ through the $m$ copies concatenates into a simple cycle. The set of crossing cycle lengths is therefore exactly

$$
\bigl\{j + p_1 + \cdots + p_m : p_1, \ldots, p_m \in S\bigr\}.
$$

Assuming the unrestricted conjecture holds, this forces two structural constraints on $S$:

* **Spread ($b \ge 2a + 1$):** Suppose instead that $b \le 2a$, and use edge joins everywhere ($j = m$). Each copy together with its outgoing edge contributes between $a + 1$ and $b + 1$. Because $b + 1 \le 2a + 1 < 2(a + 1)$, the ratio $(b + 1)/(a + 1)$ is strictly less than $2$. Thus, for sufficiently large $k$, the open interval $\bigl(2^k / (a + 1),\, 2^{k+1} / (b + 1)\bigr)$ has length greater than $1$ and lies above $3$, so it contains an integer $m \ge 3$. For that $m$, every crossing cycle has length in $[m(a + 1), m(b + 1)] \subset (2^k, 2^{k+1})$, missing every power of two. Hence the conjecture forces $b \ge 2a + 1$. (Garcia proposed the weaker bound $b \ge 2a$ for cubic two-attachment fragments; see [Garcia, Proposition 6.2 and discussion](https://arxiv.org/html/2609.04686v1#S6).)
* **Congruence ($\gcd$ of differences equals $1$):**
  * If all lengths in $S$ agree modulo an odd prime $p$, take $m = p$ copies and identify every join ($j = 0$). Then every crossing length is a sum of $p$ congruent integers and is therefore divisible by $p$, so it can never be a power of two.
  * If all lengths in $S$ share the same parity, take two copies, identify their starting terminals ($s_1 = s_2$), and join their ending terminals by an edge ($t_1 t_2$). Every crossing cycle has length $1 + p_1 + p_2$, which is odd and therefore never a power of two.

  Hence the conjecture forces the greatest common divisor of all differences $\{x - y : x, y \in S\}$ to equal $1$ (taking the gcd to be $0$ when $S$ is a singleton).

Each constraint alone is equivalent to the unrestricted conjecture for these fragments, because the three-copy counterexample above has $S = \{2\}$ (violating both spread and congruence). The ring and gcd arguments here are written proofs rather than Lean formalizations.

---

## Identification inside a smallest counterexample

**Theorem.** Every edge of a minimum-order counterexample lies on a cycle of length $3, 5, 9, 17, \ldots$ (i.e., $2^k + 1$ for some $k \ge 1$).

**Proof.** Take an edge $xy$ that lies in no triangle ($3$-cycle) and contract it to a single vertex. Because $x$ and $y$ have no common neighbor, every other vertex keeps its full degree and the merged vertex has degree at least $3 + 3 - 2 = 4$. By minimality, the contracted graph contains a dyadic cycle of length $2^k$ ($k \ge 2$). That cycle must enter the merged vertex on an edge from one endpoint of $xy$ and leave on an edge from the other (otherwise it already existed as a dyadic cycle in $G$). Restoring the edge $xy$ turns it into a simple cycle of length $2^k + 1$ passing through $xy$. $\square$

In particular, a smallest counterexample has **no bridge** and is **not bipartite** (every edge lies on an odd cycle!). This is [Ducoffe and Dumitru, Lemma 2.1](https://arxiv.org/html/2609.28594v1#S2), formalized in [Erdos64/Identification.lean](Erdos64/Identification.lean).

The same identification argument applies to **any** two distinct vertices $x, y$ whose common neighbors all have degree at least four: each common neighbor loses only one neighbor when $x$ and $y$ are merged, so minimum degree three is preserved, and the resulting dyadic cycle opens into a simple $x$-$y$ path of the same power-of-two length in $G$. In particular, this holds for every pair of vertices at distance at least three ([Erdos64/Identification.lean](Erdos64/Identification.lean)).

Counting connected components induced by degree-three vertices also yields $\ell \ge 2h + 8$ in a globally minimal counterexample (breaking order ties by edge count), where $\ell$ is the number of cubic vertices and $h$ is the number of vertices of degree at least four. [Zhou](https://airaxiv.com/papers/view/2608.0018/) obtained the same additive bound earlier. The proof in [DegreeComponents.md](DegreeComponents.md) combines the published order-40 check with an independent 11-vertex enumeration; the same component-counting method yields a tradeoff between $\ell$ and disjoint triangles as well as ratio bounds for triangle-free and bipartite counterexamples.

---

## A cubic graph with first dyadic cycle at 128

Let $f(6)$ be the smallest order of a cubic graph with no cycle of length $4, 8, 16, 32,$ or $64$. Our construction shows

$$
f(6) \le 8{,}628,
$$

improving on Garcia's bound $f(6) \le 32{,}640$ obtained from uniform replacements on a girth-17 base ([Garcia, Theorem 5.1](https://arxiv.org/html/2609.04686v1#S5)).

### Construction and verification

Start from a connected cubic base graph on $620$ vertices (cosets in $\mathrm{PSL}(2, 31)$, with $620 \cdot 3 / 2 = 930$ edges). Replace $84$ vertices by $7$-vertex gadgets and $536$ vertices by $15$-vertex gadgets, attaching the three incident base edges at each replaced vertex to its three distinct degree-two ports — for a total of $84 \cdot 7 + 536 \cdot 15 = 588 + 8{,}040 = 8{,}628$ vertices. (The exact gadget choice and port orientation at every vertex are specified in [scripts/mixed_gadget_graph.py](scripts/mixed_gadget_graph.py).)

Why does this graph avoid every dyadic cycle from $4$ through $64$?
1. **Internal cycles:** No gadget contains an internal dyadic cycle.
2. **Base-cycle projection:** Any simple cycle visiting both a gadget and its exterior must cross the gadget's three-edge boundary an even number of times — hence exactly twice — so it projects to a simple cycle in the 620-vertex base graph and crosses each visited gadget along a port-to-port path.
3. **Long base cycles ($\ge 22$):** Counting each gadget's outgoing base edge along with its internal path, every gadget contributes at least $3$ edges, so any projected cycle of base length $22$ or more has total length at least $22 \cdot 3 = 66 > 64$.
4. **Short base cycles ($\le 21$):** For all $100{,}037$ simple base cycles of length at most $21$, the Python verifier checks that the sum of minimum gadget transit lengths exceeds $64$.
5. **Independent girth check and 128-cycle:** Directly inside the 8,628-vertex expanded graph, the verifier deletes each of the $930$ connecting edges in turn and computes the shortest path between its endpoints; the minimum distance plus one is $65$, which is the exact shortest length of any cycle using a connecting edge. Finally, it constructs and verifies an explicit simple cycle of length $128$ edge by edge.

```sh
python3 scripts/mixed_gadget_graph.py
```

To retrieve the labeled adjacency lists and the 128 vertices in cyclic order from this directory, run `from scripts.mixed_gadget_graph import check_construction` and `graph, cycle = check_construction()`.

---

## Exhaustive searches for fragments and counterexamples

### Triangle expansions on small bases

Given any subcubic base graph, we can replace any subset of its vertices by triangles, attaching each incident edge to its own corner. Why is this easy to check? A base cycle of length $r$ that passes through $c$ replaced vertices can traverse each triangle using either $1$ or $2$ internal edges, so it lifts to **every** integer length in the contiguous interval $[r + c,\, r + 2c]$, while the only other simple cycles are the internal triangles themselves.

The checker [scripts/triangle_expansions.cpp](scripts/triangle_expansions.cpp) enumerates every base cycle and searches for a replacement subset whose lifted intervals all miss every power of two from $4$ upward, outputting the graph6 base and vertex bitmask for any survivor. We checked two base families (including the empty replacement set) using [McKay and Piperno's nauty 2.9.3](https://pallini.di.uniroma1.it/), which emits one representative per isomorphism class:

| Connected base family | Base orders | Bases | Surviving assignments |
| --- | --- | ---: | ---: |
| All vertices cubic | 4 through 20 | 556,471 | 0 |
| Exactly two degree-two vertices, all others cubic | 4 through 18 | 1,149,185 | 0 |

### Direct generation of bounded-terminal fragments

Direct generation also ruled out fragments with exactly two degree-two vertices and all others cubic through order $22$; the rooted search in [Bridges.md](Bridges.md) extends that bound to order $30$ and gives the corresponding edge-cut bounds for cubic counterexamples.

For unbounded maximum degree, it suffices to search for a smallest connected example (breaking order ties by fewest edges). Because deleting an edge between two vertices of degree at least four leaves a component of minimum degree at least two with at most two degree-two vertices, a smallest example has **no edge joining two vertices of degree at least four**. The generator callback [scripts/geng_terminals.c](scripts/geng_terminals.c) enforces this property and prunes whenever a new vertex closes a dyadic cycle. It ruled out all connected graphs through order **17** with minimum degree at least two, at most two degree-two vertices, and no dyadic cycle. A separate search in [Separators.md](Separators.md) extends this unrestricted-degree exclusion to order $24$, and to order $28$ with at most one degree-two vertex.

### Reproduction commands

To reproduce the triangle-expansion searches from this package with nauty's `geng` on `PATH`:

```sh
set -eo pipefail
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror scripts/triangle_expansions.cpp -o /tmp/eg64-expand
for n in $(seq 4 2 20); do
  geng -cd3D3 "$n" | /tmp/eg64-expand
done
for n in $(seq 4 2 18); do
  m=$((3*n/2-1))
  geng -cd2D3 "$n" "$m:$m" | /tmp/eg64-expand
done
```

For the direct search, set `callback` to the absolute path of `scripts/geng_terminals.c` and run these commands in a built nauty 2.9.3 source tree on x86-64:

```sh
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
```

The `-f` flag excludes $4$-cycles, and the callback rules out the larger powers of two. These generator and C++ runs are computational exclusions over the stated families.

### Three-terminal positive control and multi-gadget CSP

Allowing **three** degree-two vertices serves both as a positive control and as a compact classification. Among connected graphs through order $23$ with exactly three degree-two vertices and all other vertices cubic, **only four isomorphism classes** avoid all dyadic cycles: the triangle (order $3$), $H_7$ and $H'_7$ (order $7$, differing in their inter-terminal distances), and $H_{15}$ (order $15$). To reproduce this classification, rebuild the same callback with `-DMAX_TERMINALS=3` and run:

```sh
for n in $(seq 3 2 23); do
  m=$(((3*n-3)/2))
  /tmp/eg64-terminals-geng -cfd2D3 "$n" "$m:$m"
done
```

A second search in [scripts/gadget_csp.py](scripts/gadget_csp.py) gave each base vertex nine replacement options: an unchanged vertex, a triangle, three orientations of $H_7$, the symmetric seven-vertex piece $H'_7$, and three orientations of $H_{15}$. No assignment avoided all dyadic cycles on any of the $621$ connected cubic bases through order $14$ or any of the $972$ two-terminal bases through order $12$ (reaching expanded orders up to $210$, where the two-terminal run checks cycles inside each fragment). Run `python3 scripts/gadget_csp.py` with `geng` on `PATH` to replay it.
