# Cubic graphs with an edge cut of size one or two

Call a vertex of degree two a *terminal*. Every graph on this page is finite, simple, and connected, with all non-terminal vertices of degree three. An exhaustive search in [scripts/terminal_blocks.cpp](scripts/terminal_blocks.cpp) gives the following order bounds:

| Terminals | Every graph through this order has a power-of-two cycle | Lower bound on the order without one |
| --- | ---: | ---: |
| One | 39 | 41 |
| Two | 30 | 32 |

The last column follows from parity: a graph on $m$ vertices with $t$ terminals has degree sum $3m - t$, so $m$ and $t$ have the same parity.

## Consequences for cuts and terminal paths

Removing a bridge from a cubic graph leaves one terminal on each side. To avoid a power-of-two cycle, each side needs at least 41 vertices, giving at least **82** vertices overall. In a bridgeless cubic graph, a two-edge cut must have distinct endpoints on each side, because a shared endpoint's third edge would be a bridge. Each side then has two terminals and needs at least 32 vertices, giving at least **64** vertices overall.

There is also a path consequence for three terminals. Take a graph on at most 39 vertices with three terminals and no power-of-two cycle, and add an edge between any two nonadjacent terminals $u, v$. The resulting one-terminal graph must contain a power-of-two cycle. Deleting the new edge from that cycle leaves a simple path between $u$ and $v$ of length $2^k - 1$ for some $k \ge 2$.

## Exhaustive search

For one terminal, start by exposing the terminal and its two neighbors, trying those two neighbors both adjacent and nonadjacent. For two terminals, start with just the two terminals, again trying them adjacent and nonadjacent. At every stage, the exposed subgraph contains all edges of the target graph between exposed vertices.

Pick an exposed vertex that is still missing a neighbor. Its required neighbor must be a fresh vertex. Branch over all sets of at most three exposed neighbors for this fresh vertex that include the chosen vertex and respect the target degrees. Reject any choice containing two neighbors already joined by an exposed simple path of length $2^k - 2$, since adding the fresh vertex would close a power-of-two cycle (and every new power-of-two cycle arises this way).

With $r$ fresh vertices left, at most $3r$ missing incidences can be filled in total, and any group of exposed vertices that cannot share a fresh neighbor can fill at most $r$ of its missing incidences. Both pruning bounds discard only impossible branches. Once every degree is filled, a connected board is a counterexample and a disconnected board can never become connected, so the search finds every connected counterexample within the order cap.

```sh
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror scripts/terminal_blocks.cpp -o /tmp/eg64-terminal-blocks
/tmp/eg64-terminal-blocks two 30
NAUTY_DIR=/path/to/nauty2_9_0
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror -DTERMINAL_NAUTY \
  -isystem "$NAUTY_DIR" scripts/terminal_blocks.cpp \
  "$NAUTY_DIR/nauty.a" -o /tmp/eg64-terminal-cache
/tmp/eg64-terminal-cache one-bounded 39
```

Both runs exhaust all branches: the two-terminal run visits 57,706,154 states, and the one-terminal run visits 10,559,396 states using a 64-bit build of [nauty 2.9.0](https://pallini.di.uniroma1.it/). The one-terminal cache compares full canonical adjacency strings with the terminal distinguished, and hash collisions only evict entries. Because an existing path persists under extension and adding a degree-one leaf creates no new path between old vertices, the checker can safely reuse path tests across steps. Without nauty, the portable binary also checks `one 33` uncached in 9,640,915 states.
