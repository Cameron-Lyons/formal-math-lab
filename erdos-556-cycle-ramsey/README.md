# Erdős Problem #556: three-color nine-cycle Ramsey number R_3(C_9)

Erdős Problem #556 asks whether $R_3(C_n) \le 4n - 3$ for odd $n \ge 5$, with $R_3(C_9) = 33$ as the first open case in Radziszowski's survey. The unrestricted upper bound $R_3(C_9) \le 33$ remains open.

The Lean 4 proofs here check the known lower bound $R_3(C_9) \ge 33$ via an explicit 3-edge-coloring of $K_{32}$, prove that any 3-coloring of $K_{33}$ with a 15-vertex subset missing one color contains a monochromatic $C_9$, and reduce the 33-vertex upper bound to two remaining cases.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #556 (`erdosproblems.com/556`), three-color cycle Ramsey number $R_3(C_9) = R(C_9, C_9, C_9)$ (Radziszowski's survey §6.3.1) |
| Status | Partial and conditional results. Lower bound $R_3(C_9) \ge 33$ verified; conditional upper bound on $K_{33}$ with a 15-vertex color-missing set proved; unrestricted $R_3(C_9) \le 33$ remains open. |
| Main theorems | `Ramsey556.lowerColoring_no_monoC9`, `Ramsey556.monoC9_of_independent15`, `Ramsey556.k33_iff_final_two_cases`, `Ramsey556.splitForcesC9_iff` |
| Verification | `lake build` (Lean 4.36.0, stdlib only; checks proofs and included binary certificates) |
| Prior art | Checked 23 November 2026: lower bound 33 is known; Kohayakawa, Simonovits, and Skokan proved $R_3(C_n) = 4n - 3$ for sufficiently large odd $n$; priority for the 15-vertex conditional theorem is unverified. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-556-three-color-nine-cycle-ramsey-number). |

## Lean results

| Lean declaration | File | Result |
| --- | --- | --- |
| `Ramsey556.lowerColoring_no_monoC9` | [Ramsey556/Lower.lean](Ramsey556/Lower.lean) | Explicit 3-edge-coloring of $K_{32}$ avoiding monochromatic 9-cycles ($R_3(C_9) \ge 33$). |
| `Ramsey556.monoC9_of_independent15` | [Ramsey556/FifteenResult.lean](Ramsey556/FifteenResult.lean) | Any 3-coloring of $K_{33}$ with 15 vertices omitting one color on their internal edges contains a monochromatic $C_9$. |
| `Ramsey556.k33_iff_final_two_cases` | [Ramsey556/Remaining33.lean](Ramsey556/Remaining33.lean) | Reduces $R_3(C_9) \le 33$ to two cases, distinguished by whether some 14-vertex set misses a color. |
| `Ramsey556.splitForcesC9_iff` | [Ramsey556/SplitRamsey.lean](Ramsey556/SplitRamsey.lean) | A split graph joining an $m$-clique to an independent set ($n$ vertices total) forces a monochromatic $C_9$ in 2 colors if and only if $m \ge 13$ and $n \ge 17$. |

## Build and reproduce

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

The default target imports the proofs and checks the included certificates ([Ramsey556.lean](Ramsey556.lean)). Optional generators reproduce the finite witnesses:

* [Dense 16-vertex $C_9$-free graph certificate (`Ramsey556.Certified16`)](research/cert16/README.md)
* [Split-graph certificate generator](research/split17/generate_traces.py)

## References

* [Erdős Problems #556](https://www.erdosproblems.com/556)
* [Radziszowski, *Small Ramsey Numbers*, §6.3.1](https://www.cs.rit.edu/~spr/ElJC/ejcram18.pdf#page=61)
* [Kohayakawa, Simonovits, and Skokan, *The 3-colored Ramsey number of odd cycles*](https://users.renyi.hu/~miki/KohaSimSkokGraco.pdf)
* [Prior-art audit](../PRIOR_ART.md#erdős-556-three-color-nine-cycle-ramsey-number)
