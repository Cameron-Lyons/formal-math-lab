# The Ramsey number $R(3,10)$

$R(3,10)$ is the least number of vertices that forces a triangle or an independent set of ten in every simple graph. Exoo’s graph on 39 vertices avoids both, so the answer is at least 40. Angeltveit proved an upper bound of 41. The exact value remains open. [Exoo’s graph](https://cs.indstate.edu/ge/RAMSEY/r3.10.39) · [Angeltveit’s upper bound](https://doi.org/10.37236/12936)

## Why Exoo’s graph stops at 39 vertices

Add a vertex $v$. If two of its neighbors are adjacent, they form a triangle with $v$. Otherwise its neighbors form an independent set. Lean checks ten specific independent nine-vertex sets in Exoo’s graph and proves that at least one contains no neighbor of $v$. Those nine vertices and $v$ form an independent set of ten. This rules out every one-vertex extension of Exoo’s graph. [Ten sets and extension proof](Extension.lean)

## Lean results

| Theorem (in namespace `Ramsey310`) | What it proves |
| --- | --- |
| `ramsey_lower_bound` | The Ramsey property requires at least 40 vertices. [Graph checks](Ramsey39.lean) · [Lower bound](RamseyNumber.lean) |
| `exoo_no_one_vertex_extension` | Every choice of neighbors for a 40th vertex gives one of the two outcomes above. [Proof](Extension.lean) |
| `Circulants.order40` | Every 40-vertex circulant graph contains a triangle or ten independent vertices. [Proof](Circulants.lean) |
| `TwoOrbits.two_cycles_of_length_twenty` | The same conclusion holds whenever a symmetry rotates two disjoint cycles of 20 vertices simultaneously. [Proof](TwoOrbits.lean) |
| `SAT.value40_iff_unsat`, `SAT.value41_iff_sat` | The unrestricted SAT formula has one variable per edge of the complete graph on 40 vertices. Unsatisfiability is equivalent to the value 40. Given Angeltveit’s upper bound as a hypothesis, satisfiability is equivalent to the value 41. [Encoding and proofs](RamseySAT.lean) |

## Verification

From the repository root, run

```sh
cd ramsey-3-10
lake build
```

The package uses Lean 4.36.0 and its standard library. The two-cycle proof uses `native_decide` to validate its vertex sets and replay the LRAT certificate, so those checks trust the Lean compiler. The lower bound, extension, circulant, and SAT equivalence proofs use kernel checking. [Vertex sets](certificates/two-orbits.sets) · [LRAT certificate](certificates/two-orbits.lrat)
