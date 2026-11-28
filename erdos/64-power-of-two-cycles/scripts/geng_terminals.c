/* A nauty geng PRUNE callback for connected graphs of minimum degree two
   with a bounded number of degree-two exceptions. Compile with 32-bit geng
   and run with -cfd2, so geng itself excludes four-cycles. */
#include "nauty.h"

#ifndef MAX_TERMINALS
#define MAX_TERMINALS 2
#endif

static int path_to_neighbor(const graph *g, int current, setword unused,
                            setword endpoints, int remaining) {
    setword choices = g[current] & unused;
    if (remaining == 1) return (choices & endpoints) != 0;
    while (choices) {
        int next = FIRSTBITNZ(choices);
        choices ^= bit[next];
        if (path_to_neighbor(g, next, unused ^ bit[next], endpoints, remaining - 1))
            return 1;
    }
    return 0;
}

int prune_terminals(graph *g, int n, int maxn) {
    int exceptions = 0;
    setword heavy = 0;
    for (int v = 0; v < n; ++v) {
        int degree = POPCOUNT(g[v]);
        if (n == maxn && degree < 3 && ++exceptions > MAX_TERMINALS) return 1;
        if (degree >= 4) {
            /* Any minimum-order, minimum-size example has no such edge:
               delete it and retain a component. This test is hereditary. */
            if (g[v] & heavy) return 1;
            heavy |= bit[v];
        }
    }
    /* Ancestors were already checked. Test cycles through the newest vertex
       by joining two of its neighbors with a simple path outside it. */
    int newest = n - 1;
    setword neighbors = g[newest];
    while (neighbors) {
        int start = FIRSTBITNZ(neighbors);
        neighbors ^= bit[start];
        for (int length = 8; neighbors && length <= n; length *= 2)
            if (path_to_neighbor(g, start, ~(bit[start] | bit[newest]), neighbors,
                                 length - 2))
                return 1;
    }
    return 0;
}
