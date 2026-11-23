# Erdős #556 — Three-color cycle Ramsey numbers

The conjectured value of the three-color Ramsey number $R_3(C_9)$ is 33.
Lean verifies the lower-bound coloring on 32 vertices and proves that a
three-coloring of $K_{33}$ contains a monochromatic nine-cycle if some set
of 15 vertices omits a color on its internal edges. The unrestricted upper
bound remains open. [Problem statement](https://www.erdosproblems.com/556) ·
[Ramsey survey, §6.3.1](https://www.cs.rit.edu/~spr/ElJC/ejcram18.pdf#page=61)

| Lean declaration | Result |
| --- | --- |
| [`Ramsey556.lowerColoring_no_monoC9`](Ramsey556/Lower.lean) | An explicit three-coloring of $K_{32}$ avoids monochromatic nine-cycles. |
| [`Ramsey556.monoC9_of_independent15`](Ramsey556/FifteenResult.lean) | Fifteen vertices missing a color force a monochromatic nine-cycle somewhere in $K_{33}$. |
| [`Ramsey556.k33_iff_final_two_cases`](Ramsey556/Remaining33.lean) | Reduces the upper bound to two cases, distinguished by whether a set of 14 vertices misses a color. |
| [`Ramsey556.splitForcesC9_iff`](Ramsey556/SplitRamsey.lean) | A clique of size $m$ joined to an independent set, with $n$ vertices total, forces a monochromatic nine-cycle in two colors exactly when $m \ge 13$ and $n \ge 17$. |

## Build

Run from this directory with Lean 4.36.0.

```sh
lake build
```

The default target imports the proofs and checks the included certificates.
The optional generators reproduce the finite witnesses. [Lean entry point](Ramsey556.lean) ·
[16-vertex certificate](research/cert16/README.md) ·
[Split-graph certificate generator](research/split17/generate_traces.py)
