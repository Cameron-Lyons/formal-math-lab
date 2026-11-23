# Dense 16-vertex graph certificate

Run `lake build Ramsey556.Certified16` from the project root to check that every 16-vertex graph with at least 60 edges and no nine-cycle is bipartite. The build reads the included binary witnesses and checks their contents with Lean's kernel.

To reproduce the witnesses, unpack nauty 2.9.3, run `./configure` in its source directory, then run the following from the project root.

```sh
research/cert16/generate.sh /path/to/nauty2_9_3
lake build Ramsey556.Certified16
```

The generator requires Bash, make, C and C++17 compilers with 128-bit integer support, and Python 3. It builds `geng` with a pruning function for complements of dense graphs. It stores graph6 representatives and text witnesses under `.lake/cert16-generation` and regenerates the Lean tables, binary witness files, and layer modules under `Ramsey556/Cert16`. Each generated strip records its binary file’s SHA-256 digest so changes made by regeneration invalidate its Lake build trace.

Lean starts from the one-vertex graph. At each order it covers every neighborhood that preserves the required density, excluding pairs joined by a checked seven-edge path. Adding a vertex adjacent to both endpoints would create a nine-cycle. Each surviving neighborhood comes with a vertex permutation into the next table. After fifteen extensions, the terminal table has 30 graphs. Each has a checked bipartition. Minimum-degree deletion ensures that the induction covers every graph in the theorem.
