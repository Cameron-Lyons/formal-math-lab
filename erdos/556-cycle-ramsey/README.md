# Erdős Problem #556: three-color nine-cycle Ramsey number R_3(C_9)

Color every edge of the complete graph $K_N$ (where every pair of $N$ vertices is connected by an edge) with three colors. The **three-color cycle Ramsey number** $R_3(C_n)$ is the smallest $N$ that *forces* a monochromatic $n$-cycle $C_n$ (a closed loop of $n$ edges all in the same color), no matter how the edges are colored.

**Erdős Problem #556** asks whether $R_3(C_n) \le 4n - 3$ for every odd $n \ge 5$ (matching the known lower bound $4n - 3$, which Kohayakawa, Simonovits, and Skokan proved tight for all sufficiently large odd $n$). In Radziszowski's survey (§6.3.1), **$R_3(C_9) = 33$** is the first open case.

**What is proved here vs. what remains open:**

* **Proved unconditionally in Lean 4:** the known lower bound $R_3(C_9) \ge 33$ (via an explicit 3-edge-coloring of $K_{32}$ avoiding monochromatic $C_9$), an exact 2-color Ramsey threshold for split graphs (`splitForcesC9_iff`), and the 15-vertex conditional theorem on $K_{33}$ (every 3-coloring of $K_{33}$ containing 15 vertices whose internal edges omit one color must contain a monochromatic $C_9$).
* **Reduction proved in Lean 4:** the full upper bound $R_3(C_9) \le 33$ reduces cleanly to two remaining cases on $K_{33}$, depending on whether some 14-vertex subset omits a color (`k33_iff_final_two_cases`).
* **Still open:** the unrestricted upper bound $R_3(C_9) \le 33$.

## At a glance

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #556 (`erdosproblems.com/556`), three-color cycle Ramsey number $R_3(C_9) = R(C_9, C_9, C_9)$ (Radziszowski's survey §6.3.1) |
| Status | Partial and conditional results. Verifies $R_3(C_9) \ge 33$ and proves the 15-vertex conditional bound on $K_{33}$; unrestricted $R_3(C_9) \le 33$ is still open. |
| Main theorems | `Ramsey556.lowerColoring_no_monoC9`, `Ramsey556.monoC9_of_independent15`, `Ramsey556.k33_iff_final_two_cases`, `Ramsey556.splitForcesC9_iff` |
| Verification | `lake build` (Lean 4.36.0, stdlib only; checks proofs and included binary certificates) |
| Prior art | Checked 23 November 2026. The lower bound 33 is known, and Kohayakawa, Simonovits, and Skokan proved $R_3(C_n) = 4n - 3$ for all sufficiently large odd $n$. Priority for the 15-vertex conditional theorem is unverified. |

## Lean results

Here a **split graph** joining an $m$-clique to an $(n - m)$-vertex independent set is the $n$-vertex graph containing every edge except pairs lying wholly outside the $m$-clique.

| Lean declaration | File | Result |
| --- | --- | --- |
| `Ramsey556.lowerColoring_no_monoC9` | [Ramsey556/Lower.lean](Ramsey556/Lower.lean) | Checks an explicit 3-edge-coloring of $K_{32}$ with no monochromatic 9-cycle ($R_3(C_9) \ge 33$). |
| `Ramsey556.monoC9_of_independent15` | [Ramsey556/FifteenResult.lean](Ramsey556/FifteenResult.lean) | Every 3-coloring of $K_{33}$ with 15 vertices whose internal edges omit one color contains a monochromatic $C_9$. |
| `Ramsey556.k33_iff_final_two_cases` | [Ramsey556/Remaining33.lean](Ramsey556/Remaining33.lean) | Reduces $R_3(C_9) \le 33$ to two cases, depending on whether some 14-vertex set misses a color. |
| `Ramsey556.splitForcesC9_iff` | [Ramsey556/SplitRamsey.lean](Ramsey556/SplitRamsey.lean) | A split graph joining an $m$-clique to an independent set ($n$ vertices total) forces a monochromatic $C_9$ in 2 colors if and only if $m \ge 13$ and $n \ge 17$. |

## Build and reproduce

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

The default target imports all proofs and checks the included binary certificates ([Ramsey556.lean](Ramsey556.lean)).

## References

* [Erdős Problems #556](https://www.erdosproblems.com/556)
* [Radziszowski, *Small Ramsey Numbers*, §6.3.1](https://www.cs.rit.edu/~spr/ElJC/ejcram18.pdf#page=61)
* [Kohayakawa, Simonovits, and Skokan, *The 3-colored Ramsey number of odd cycles*](https://users.renyi.hu/~miki/KohaSimSkokGraco.pdf)
