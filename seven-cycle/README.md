# Seven-cycle Ramsey threshold R_3^2(C_7) = 11 (at most two color changes, Allen et al. Problem 22) — Lean 4 proof

**Exact threshold proved in Lean 4: $R_3^2(C_7) = 11$.** Color every edge of the complete graph $K_n$ red, green, or blue. A *color change* (*colour change*) along a cycle occurs whenever two consecutive edges have different colors, **including** the transition where the last edge meets the first. (Merely using at most two colors is a weaker condition.)

Then **$n = 11$** is the smallest number of vertices that guarantees a 7-cycle ($C_7$) with at most 2 cyclic color changes in every 3-edge-coloring of $K_n$. This settles the $C_7$ finite case of **Problem 22** of Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz (`arXiv:2607.03243`).

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Seven-cycle Ramsey threshold** `R_3^2(C_7) = 11` (`R₃²(C₇) = 11`), 3-edge-coloring of $K_n$ forcing a $C_7$ with at most 2 cyclic color/colour changes, Allen–Böttcher–Clemens–Hamann–Skokan–Taraz (`Allen Bottcher Clemens Hamann Skokan Taraz`, `arXiv:2607.03243v1`, Problem 22) |
| **Status** | **Case $C_7$ completely proved in Lean 4 ($R_3^2(C_7) = 11$).** The general odd-cycle family in Problem 22 remains open. |
| **Main Lean theorems** | `SevenCycle.exact_threshold (n : Nat) : ForcesSeven n ↔ 11 ≤ n`, `SevenCycle.eleven_forces` in [SevenCycle.lean](SevenCycle.lean) |
| **Verification** | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof) |
| **Prior-art status** | Checked **22 November 2026**: no earlier proof or Lean formalization of `R_3^2(C_7) = 11` located (bounded search, not a claim of absolute priority). The lower-bound coloring specializes the paper's colored-$K_4$ template. See [PRIOR_ART.md](../PRIOR_ART.md#seven-cycle). |

## Proof overview

* **Lower bound ($R_3^2(C_7) \ge 11$, why $K_{10}$ fails):** partition 10 vertices into one apex vertex and three 3-vertex groups labeled red, green, and blue. Color every edge inside each group and from the apex to that group with the group's color, and color every edge between two different groups with the third color (specializing the colored-$K_4$ template of Allen et al.). Lean checks that every 7-cycle in this coloring of $K_{10}$ has at least 3 cyclic color changes. [Lower-bound proof](SevenCycle/Lower.lean)
* **Upper bound ($R_3^2(C_7) \le 11$, why $K_{11}$ works):** pick any vertex of $K_{11}$. Among its 10 incident edges, at least 4 share one color by the pigeonhole principle. Retaining that vertex, those 4 monochromatic neighbors, and 5 other vertices, Lean checks (`SevenCycle.star_forces_seven`) that every 3-coloring of the remaining edges forces a 7-cycle with at most 2 cyclic color changes. [Upper-bound proof](SevenCycle/CheckedSeeds.lean)

## Check the proof

Run from this directory with Lean **4.36.0** (standard library only):

```sh
lake build
```

## References

* [Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz, `arXiv:2607.03243v1`, Problem 22](https://arxiv.org/html/2607.03243v1#Thmtheorem22)
* [Main Lean theorem](SevenCycle.lean)
* [Dated prior-art audit](../PRIOR_ART.md#seven-cycle)
