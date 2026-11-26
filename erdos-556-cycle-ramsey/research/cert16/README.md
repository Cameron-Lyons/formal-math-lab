# Dense 16-vertex C_9-free graph certificate (Erdős #556)

This certificate supports the [Erdős #556 / $R_3(C_9)$ Lean 4 project](../../README.md). Run `lake build Ramsey556.Certified16` from the `erdos-556-cycle-ramsey` root directory to verify that every 16-vertex simple graph with at least 60 edges and no 9-cycle ($C_9$) is bipartite. Lean's kernel reads and checks the included binary witnesses.

## Regenerating the witnesses

To rebuild the witnesses from scratch, unpack `nauty` 2.9.3, run `./configure` in its source directory, and run these commands from the `erdos-556-cycle-ramsey` root directory:

```sh
research/cert16/generate.sh /path/to/nauty2_9_3
lake build Ramsey556.Certified16
```

The generator needs Bash, `make`, C23 and C++23 compilers with 128-bit integer support, and Python 3. It builds `geng` with a pruning function for complements of dense graphs and saves `graph6` representatives and text witnesses under `.lake/cert16-generation`. It then regenerates the Lean tables, binary witness files, and layer modules under `Ramsey556/Cert16`. Each generated strip records the SHA-256 digest of its binary file so Lake rebuilds it whenever the witnesses change.

## How the kernel check works

Lean starts from the 1-vertex graph and extends one vertex at a time. At each size, it checks every neighborhood that keeps the required edge density, skipping any pair already joined by a checked 7-edge path (since a new vertex adjacent to both endpoints would close a 9-cycle). Each surviving neighborhood maps into the next table via an explicit vertex permutation. After 15 extensions, the final table holds 30 graphs, each with a checked bipartition. Deleting a minimum-degree vertex shows by induction that this search covers every graph in the theorem.
