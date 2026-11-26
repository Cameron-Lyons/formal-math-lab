# Seven-cycle Ramsey threshold R_3^2(C_7) = 11

Color every edge of the complete graph $K_n$ red, green, or blue. A *color change* along a cycle occurs whenever two consecutive edges have different colors, including where the last edge meets the first (using at most two colors is a weaker condition).

The Lean 4 proof here proves $R_3^2(C_7) = 11$: $n = 11$ is the smallest vertex count that forces a 7-cycle ($C_7$) with at most 2 cyclic color changes in every 3-edge-coloring of $K_n$. This settles the $C_7$ case of Problem 22 of Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz (`arXiv:2607.03243`).

| Field | Summary |
| --- | --- |
| Problem | Seven-cycle Ramsey threshold $R_3^2(C_7) = 11$, Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz (`arXiv:2607.03243v1`, Problem 22) |
| Status | Case $C_7$ proved in Lean 4 ($R_3^2(C_7) = 11$). The general odd-cycle family in Problem 22 remains open. |
| Main theorems | `SevenCycle.exact_threshold (n : Nat) : ForcesSeven n ↔ 11 ≤ n`, `SevenCycle.eleven_forces` in [SevenCycle.lean](SevenCycle.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof) |
| Prior art | Checked 22 November 2026: no earlier proof or Lean formalization of $R_3^2(C_7) = 11$ was found (bounded search, not a claim of absolute priority). The lower-bound coloring specializes the paper's colored-$K_4$ template. See [PRIOR_ART.md](../PRIOR_ART.md#seven-cycle). |

## Proof overview

* Lower bound ($R_3^2(C_7) \ge 11$, [SevenCycle/Lower.lean](SevenCycle/Lower.lean)): split 10 vertices into one apex vertex and three 3-vertex groups labeled red, green, and blue. Color every edge inside each group and from the apex to that group with the group's color, and color every edge between two different groups with the third color (specializing the colored-$K_4$ template of Allen et al.). Lean checks that every 7-cycle in this coloring of $K_{10}$ has at least 3 cyclic color changes.
* Upper bound ($R_3^2(C_7) \le 11$, [SevenCycle/CheckedSeeds.lean](SevenCycle/CheckedSeeds.lean)): pick any vertex of $K_{11}$. By the pigeonhole principle, at least 4 of its 10 incident edges share one color. Keeping that vertex, those 4 monochromatic neighbors, and 5 other vertices, Lean checks (`SevenCycle.star_forces_seven`) that every 3-coloring of the remaining edges forces a 7-cycle with at most 2 cyclic color changes.

## Check the proof

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

## References

* [Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz, `arXiv:2607.03243v1`, Problem 22](https://arxiv.org/html/2607.03243v1#Thmtheorem22)
* [SevenCycle.lean](SevenCycle.lean)
* [Prior-art audit](../PRIOR_ART.md#seven-cycle)
