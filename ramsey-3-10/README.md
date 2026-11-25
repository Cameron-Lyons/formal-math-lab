# Classical Ramsey number R(3, 10)

The classical Ramsey number $R(3, 10)$ is the smallest $N$ such that every simple graph on $N$ vertices contains a triangle ($K_3$) or an independent set of size 10 ($\overline{K_{10}}$). Geoffrey Exoo's 39-vertex graph gives $R(3, 10) \ge 40$, and Vigleik Angeltveit (2025) proved $R(3, 10) \le 41$. Whether $R(3, 10)$ is 40 or 41 remains open.

The Lean 4 proofs here check Exoo's 39-vertex witness ($R(3, 10) \ge 40$), prove that no one-vertex extension of Exoo's graph to 40 vertices avoids both $K_3$ and $\overline{K_{10}}$, rule out all 40-vertex circulant graphs and all 40-vertex graphs invariant under simultaneous rotation of two 20-vertex cycles, and prove the equivalence between $R(3, 10) \in \{40, 41\}$ and the unrestricted 40-vertex SAT formula.

| Field | Summary |
| --- | --- |
| Problem | Classical Ramsey number $R(3, 10)$ ($40 \le R(3, 10) \le 41$), Exoo (1989) 39-vertex graph, Angeltveit (2025) upper bound 41 |
| Status | Lower bound 40 verified and order-40 extension/symmetry obstructions proved; choice between 40 and 41 remains open. |
| Main theorems | `Ramsey310.ramsey_lower_bound`, `exoo_no_one_vertex_extension`, `Circulants.order40`, `TwoOrbits.two_cycles_of_length_twenty`, `SAT.value40_iff_unsat`, `SAT.value41_iff_sat` |
| Verification | `lake build` (Lean 4.36.0, stdlib only; lower bound, extension, circulant, and SAT equivalence are kernel-checked; two-cycle LRAT check uses `native_decide`) |
| Prior art | Checked 23 November 2026: Exoo (1989) proved $R(3, 10) \ge 40$, Angeltveit (2025) proved $R(3, 10) \le 41$, and Harborth and Krause (2003) and Coniglio et al. (2026) already reported the circulant bound 38. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Why Exoo's 39-vertex graph cannot be extended by one vertex

Add a 40th vertex $v$ to Exoo's 39-vertex graph. If two neighbors of $v$ are adjacent, they form a triangle with $v$; otherwise the neighborhood of $v$ is an independent set. Lean checks ten explicit 9-vertex independent sets in Exoo's graph and proves that at least one of them contains no neighbor of $v$. Adjoining $v$ to that 9-set yields an independent set of size 10, ruling out every one-vertex extension ([Extension.lean](Extension.lean)).

## Lean results

| Theorem (namespace `Ramsey310`) | File | What it proves |
| --- | --- | --- |
| `ramsey_lower_bound` | [Ramsey39.lean](Ramsey39.lean), [RamseyNumber.lean](RamseyNumber.lean) | Exoo's 39-vertex graph is triangle-free with no independent 10-set, proving $R(3, 10) \ge 40$. |
| `exoo_no_one_vertex_extension` | [Extension.lean](Extension.lean) | Every choice of neighbors for a 40th vertex added to Exoo's graph creates a triangle or an independent 10-set. |
| `Circulants.order40` | [Circulants.lean](Circulants.lean) | Every 40-vertex circulant graph contains a triangle or an independent 10-set. |
| `TwoOrbits.two_cycles_of_length_twenty` | [TwoOrbits.lean](TwoOrbits.lean) | Every 40-vertex graph invariant under simultaneous rotation of two disjoint 20-cycles contains a triangle or an independent 10-set. |
| `SAT.value40_iff_unsat`, `SAT.value41_iff_sat` | [RamseySAT.lean](RamseySAT.lean) | For the unrestricted 40-vertex SAT formula (one variable per edge of $K_{40}$), unsatisfiability is equivalent to $R(3, 10) = 40$, and (assuming Angeltveit's $R(3, 10) \le 41$) satisfiability is equivalent to $R(3, 10) = 41$. |

## Verification

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

The lower bound, one-vertex extension exclusion, circulant exclusion, and SAT equivalence are kernel-checked. The two-cycle theorem uses `native_decide` to validate its vertex sets and replay its LRAT certificate ([certificates/two-orbits.sets](certificates/two-orbits.sets), [certificates/two-orbits.lrat](certificates/two-orbits.lrat)), trusting the Lean compiler and runtime for those finite checks.

## References

* [Exoo (1989)](https://doi.org/10.1137/0402043) and [Exoo's 39-vertex matrix](https://cs.indstate.edu/ge/RAMSEY/r3.10.39)
* [Angeltveit (2025), Theorem 1 ($R(3, 10) \le 41$)](https://doi.org/10.37236/12936)
* [Harborth and Krause (2003), Table 1](https://www.researchgate.net/profile/Heiko-Harborth/publication/265670071_Ramsey_numbers_for_circulant_colorings/links/617430c6eef53e51e1d63351/Ramsey-numbers-for-circulant-colorings.pdf) and [Coniglio et al. (`arXiv:2608.18769v1`, Table 8)](https://arxiv.org/html/2608.18769v1#S8.T8)
* [Prior-art audit](../PRIOR_ART.md)
