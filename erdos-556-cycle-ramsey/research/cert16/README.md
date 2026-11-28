# Dense 16-vertex C_9-free graph certificate (Erdős #556)

This certificate supports the [Erdős #556 / $R_3(C_9)$ Lean 4 project](../../README.md). It proves a sharp extremal graph-theory lemma: **every 16-vertex simple graph with at least 60 edges and no 9-cycle ($C_9$) must be bipartite** (meaning its vertices split into two groups with all edges going *between* the groups, so it has no odd cycles at all).

Run `lake build Ramsey556.Certified16` from the `erdos-556-cycle-ramsey` root directory to verify the theorem. Lean's kernel reads and checks the included binary witnesses directly—the external generator is outside the trust boundary.

## How the kernel check works

**The big idea.** Take any 16-vertex $C_9$-free graph with at least 60 edges and repeatedly delete a vertex of *minimum degree* until only 1 vertex remains. Because removing a minimum-degree vertex deletes at most the average degree, every intermediate graph in the chain stays above a tight minimum edge density.

Lean verifies this process in reverse—starting from the 1-vertex graph and extending **one vertex at a time** across 15 layers:

1. **Exhaustive neighborhood check with 7-path pruning:** At each size, Lean tests every possible neighborhood for the new vertex that maintains the required edge density. It immediately skips any neighborhood containing two vertices already linked by a checked 7-edge path, because connecting the new vertex to both endpoints of that path would close a 9-cycle ($C_9$).
2. **Canonical witness mapping:** Every surviving extended graph is matched to an entry in the next layer's canonical table via an explicit vertex permutation stored in the binary witness files.
3. **Final bipartition check:** After 15 extensions, the 16-vertex table contains just **30 graphs**, and Lean checks an explicit bipartition for every one of them.

By induction (deleting a minimum-degree vertex at each step), this layered search covers every 16-vertex $C_9$-free graph with at least 60 edges.

## Regenerating the witnesses

To rebuild the witnesses from scratch, unpack `nauty` 2.9.3, run `./configure` in its source directory, and run these commands from the `erdos-556-cycle-ramsey` root directory:

```sh
research/cert16/generate.sh /path/to/nauty2_9_3
lake build Ramsey556.Certified16
```

**Requirements and pipeline:** The generator needs Bash, `make`, C23 and C++23 compilers with 128-bit integer support, and Python 3. It builds `geng` with a custom pruning function for complements of dense graphs and saves `graph6` representatives and text witnesses under `.lake/cert16-generation`. It then regenerates the Lean tables, binary witness files, and layer modules under `Ramsey556/Cert16`. Each generated strip records the SHA-256 digest of its binary file so Lake automatically rebuilds it whenever the witnesses change.
