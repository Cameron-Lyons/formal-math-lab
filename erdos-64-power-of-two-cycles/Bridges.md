# Cubic graphs with an edge cut of size one or two

A terminal is a vertex of degree two. Here all graphs are finite, simple and connected, and every other vertex has degree three. An exhaustive search gives the following bounds. [Checker](scripts/terminal_blocks.cpp)

| Terminals | Every graph through this order has a power-of-two cycle | Lower bound on the order without one |
|---|---:|---:|
| One | 39 | 41 |
| Two | 30 | 32 |

The last column follows from parity. A graph with $m$ vertices and $t$ terminals has degree sum $3m-t$, so $m$ and $t$ have the same parity.

## Consequences for cuts and terminal paths

Deleting a bridge in a cubic graph leaves one terminal on each side. Each side needs at least 41 vertices to avoid a power-of-two cycle, giving **82** in total. In a bridgeless cubic graph, a two-edge cut has distinct endpoints on each side. Otherwise their common endpoint's third edge would be a bridge. Each side has two terminals and needs at least 32 vertices, giving **64** in total.

There is also a path consequence for three terminals. In a graph on at most 39 vertices with three terminals and no power-of-two cycle, add an edge between any two nonadjacent terminals $u,v$. The resulting one-terminal graph has a power-of-two cycle. Removing the new edge from that cycle gives a simple $u$–$v$ path of length $2^k-1$ with $k\ge2$.

## Exhaustive search

With one terminal, expose it and its two neighbors and try the neighbors adjacent and nonadjacent. With two terminals, start with just the terminals and try them adjacent and nonadjacent. The exposed graph always includes every edge of the target between exposed vertices.

Choose a vertex still missing a neighbor. Its required neighbor is fresh. Try every set of at most three exposed neighbors for the fresh vertex that includes the chosen vertex and respects the prescribed degrees. Reject two proposed neighbors if a simple path of length $2^k-2$ already joins them. This test detects every new power-of-two cycle, since removing the fresh vertex from such a cycle leaves exactly that path.

With $r$ fresh vertices still available, at most $3r$ missing incidences can be filled. For any group of exposed vertices that cannot share a fresh neighbor, at most $r$ of their incidences can be filled. These bounds discard only impossible branches. When all degrees are filled, a connected board is a candidate and a disconnected board can never become connected. Thus every connected candidate would be found.

```sh
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror scripts/terminal_blocks.cpp -o /tmp/eg64-terminal-blocks
/tmp/eg64-terminal-blocks two 30
NAUTY_DIR=/path/to/nauty2_9_0
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror -DTERMINAL_NAUTY \
  -isystem "$NAUTY_DIR" scripts/terminal_blocks.cpp \
  "$NAUTY_DIR/nauty.a" -o /tmp/eg64-terminal-cache
/tmp/eg64-terminal-cache one-bounded 39
```

The two-terminal run visits 57,706,154 states. The one-terminal run visits 10,559,396 using a 64-bit build of nauty 2.9.0. Both exhaust all branches. The one-terminal cache compares full canonical adjacency strings with the terminal distinguished. Hash collisions only evict entries. A path already found persists under extension, and adding a leaf creates no new path between old vertices. These two observations allow the checker to reuse its path tests. The portable executable also runs `one 33` without caching, taking 9,640,915 states. [Source of nauty](https://pallini.di.uniroma1.it/)
