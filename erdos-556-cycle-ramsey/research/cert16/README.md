# Dense 16-vertex C_9-free graph certificate (Erdős #556)

This certificate supports the [Erdős #556 / $R_3(C_9)$ Lean 4 project](../../README.md). Run `lake build Ramsey556.Certified16` from the `erdos-556-cycle-ramsey` project root to verify that every 16-vertex simple graph with at least 60 edges and no 9-cycle ($C_9$) is bipartite. The build reads the included binary witnesses and checks their contents with Lean's kernel.

## Regenerating the witnesses

To reproduce the witnesses from scratch, unpack `nauty` 2.9.3, run `./configure` in its source directory, and run the following from the `erdos-556-cycle-ramsey` project root:

```sh
research/cert16/generate.sh /path/to/nauty2_9_3
lake build Ramsey556.Certified16
```

The generator requires Bash, `make`, C23 and C++23 compilers with 128-bit integer support, and Python 3. It builds `geng` with a pruning function for complements of dense graphs, stores `graph6` representatives and text witnesses under `.lake/cert16-generation`, and regenerates the Lean tables, binary witness files, and layer modules under `Ramsey556/Cert16`. Each generated strip records its binary file's SHA-256 digest so regeneration invalidates its Lake build trace.

## How the kernel check works

Lean starts from the 1-vertex graph. At each order it covers every neighborhood that preserves the required density, excluding pairs joined by a checked 7-edge path (adding a vertex adjacent to both endpoints would create a 9-cycle). Each surviving neighborhood comes with a vertex permutation into the next table. After 15 extensions, the terminal table has 30 graphs, each with a checked bipartition. Minimum-degree deletion ensures that the induction covers every graph in the theorem.
