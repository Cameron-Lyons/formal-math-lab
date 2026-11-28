# Cubic Graphs with an Edge Cut of Size One or Two

Suppose a connected cubic counterexample to Erdős Problem #64 can be split into two parts by cutting just one edge (a *bridge*) or two edges (a *2-edge cut*). Removing those cut edges leaves each side almost cubic: every vertex keeps degree three except for one or two degree-two vertices — called *terminals* — where the cut edges used to attach.

By exhaustively searching these one-terminal and two-terminal building blocks with [scripts/terminal_blocks.cpp](scripts/terminal_blocks.cpp), we establish sharp order thresholds for each block type and deduce that any connected cubic counterexample has at least **82 vertices** if it has a bridge, and at least **64 vertices** if it is bridgeless with a 2-edge cut.

---

## Order bounds for one- and two-terminal blocks

Every graph on this page is finite, simple, and connected, with all non-terminal vertices of degree three. Exhaustive search gives the following thresholds:

| Terminals | Every graph through this order has a power-of-two cycle | Lower bound on the order without one |
| --- | ---: | ---: |
| One | 39 | 41 |
| Two | 30 | 32 |

The jump of $2$ in the last column comes from the handshaking lemma: a graph on $m$ vertices with $t$ terminals has degree sum $3m - t$, which must be even, so $m$ and $t$ always share the same parity (odd orders for one terminal, even orders for two terminals).

---

## Consequences for cuts and terminal paths

* **Cubic graphs with a bridge ($\ge 82$ vertices):** Deleting a bridge from a cubic graph leaves two disjoint connected components, each with exactly one terminal. To avoid a power-of-two cycle, each side needs at least $41$ vertices, giving at least **$41 + 41 = 82$** vertices overall.
* **Bridgeless cubic graphs with a 2-edge cut ($\ge 64$ vertices):** In a bridgeless cubic graph, the two cut edges cannot share an endpoint on either side — if a vertex $v$ met both cut edges, then moving $v$ to the other side would leave $v$'s third incident edge as a bridge. Deleting the two cut edges therefore leaves two disjoint connected components, each with two distinct terminals. Each side needs at least $32$ vertices, giving at least **$32 + 32 = 64$** vertices overall.
* **A forced path length for three-terminal blocks:** Take any graph on at most $39$ vertices with three terminals and no power-of-two cycle, and add an edge between any two nonadjacent terminals $u$ and $v$. The resulting graph has only one terminal and at most $39$ vertices, so it must contain a power-of-two cycle. That cycle must use the newly added edge $uv$; deleting $uv$ leaves a simple $u$-$v$ path of length $2^k - 1$ for some $k \ge 2$.

---

## How the exhaustive search works

Rather than enumerating arbitrary graphs from scratch, the checker grows a partial *exposed* subgraph one vertex at a time while preserving the invariant that **every edge of the target graph between already-exposed vertices is already present**:

1. **Initial seeds:**
   * For **one terminal**, expose the terminal and its two neighbors, branching over whether those two neighbors are adjacent or nonadjacent.
   * For **two terminals**, expose just the two terminals, again branching over whether they are adjacent or nonadjacent.
2. **Vertex expansion:** Pick an exposed vertex that is still missing a neighbor. By the invariant, its missing neighbor must be a *fresh* vertex outside the exposed subgraph. Branch over all subsets of at most three exposed neighbors for this fresh vertex that include the chosen vertex and stay within each vertex's target degree ($2$ for terminals, $3$ for all others).
3. **Cycle rejection:** Reject any neighborhood choice that includes two exposed vertices already joined by an exposed simple path of length $2^k - 2$, because adding the fresh vertex would immediately close a cycle of length $2^k$ — and every newly created power-of-two cycle arises in exactly this way.
4. **Capacity pruning:** Suppose $r$ fresh vertices remain under the order cap. Then at most $3r$ missing incidences can be filled in total. Moreover, any group of exposed vertices that cannot share a fresh neighbor (for instance, because every pair in the group is already forbidden from having a common neighbor) can fill at most $r$ of its combined missing incidences. Both bounds discard only provably impossible branches.
5. **Termination:** Once every exposed vertex meets its target degree, a connected graph is a counterexample, while a disconnected graph can never become connected later. The search therefore finds every connected counterexample within the order cap.

### Reproducing the runs

```sh
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror scripts/terminal_blocks.cpp -o /tmp/eg64-terminal-blocks
/tmp/eg64-terminal-blocks two 30
NAUTY_DIR=/path/to/nauty2_9_0
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror -DTERMINAL_NAUTY \
  -isystem "$NAUTY_DIR" scripts/terminal_blocks.cpp \
  "$NAUTY_DIR/nauty.a" -o /tmp/eg64-terminal-cache
/tmp/eg64-terminal-cache one-bounded 39
```

Both runs exhaust every branch and find no counterexamples:
* The **two-terminal** run through order $30$ visits **57,706,154** states.
* The **one-terminal** run through order $39$ visits **10,559,396** states using a 64-bit build of [nauty 2.9.0](https://pallini.di.uniroma1.it/).

For soundness of the optimizations: the one-terminal transposition table compares full canonical adjacency strings with the terminal distinguished, and hash collisions only evict entries (never causing false hits). Because an existing path persists under extension and adding a degree-one leaf creates no new path between previously exposed vertices, the checker can also safely reuse path tests across steps. Without nauty, the portable binary checks `one 33` uncached in **9,640,915** states.
