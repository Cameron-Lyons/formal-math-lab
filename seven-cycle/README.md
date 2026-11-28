# Seven-cycle Ramsey threshold $R_3^2(C_7) = 11$

Color every edge of the complete graph $K_n$ (all pairs of $n$ vertices joined by edges) red, green, or blue. Walk around a 7-cycle $v_1 \to v_2 \to \cdots \to v_7 \to v_1$ and count how many times the edge color switches between consecutive edges—**including** where the 7th edge wraps back around to the 1st. Such a switch is called a **cyclic color change**.

> **Concrete example:** A 7-cycle with edge colors `R-R-R-G-G-G-G` has **2** cyclic color changes (red $\to$ green after edge 3, and green $\to$ red wrapping from edge 7 back to edge 1): it splits into two solid monochromatic arcs. By contrast, `R-G-R-G-R-G-G` also uses only two colors, yet has **6** cyclic color changes (`R→G`, `G→R`, `R→G`, `G→R`, `R→G`, and `G→R` at wrap-around). Having at most 2 cyclic color changes is therefore much stricter than merely using at most two colors—it forces the cycle to be either monochromatic (0 changes) or two contiguous monochromatic segments (2 changes).

The Ramsey threshold $R_3^2(C_7)$ is the smallest number of vertices $n$ such that *every* 3-edge-coloring of $K_n$ contains a 7-cycle ($C_7$) with at most 2 cyclic color changes. The Lean 4 proof here settles the $C_7$ case of Problem 22 of Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz (`arXiv:2607.03243`), proving the exact value **$R_3^2(C_7) = 11$**.

| Field | Summary |
| --- | --- |
| Problem | Seven-cycle Ramsey threshold $R_3^2(C_7) = 11$, Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz (`arXiv:2607.03243v1`, Problem 22) |
| Status | Case $C_7$ proved in Lean 4 ($R_3^2(C_7) = 11$). The general odd-cycle family in Problem 22 remains open. |
| Main theorems | `SevenCycle.exact_threshold (n : Nat) : ForcesSeven n ↔ 11 ≤ n`, `SevenCycle.eleven_forces` in [SevenCycle.lean](SevenCycle.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof) |
| Prior art | Checked 22 November 2026: no earlier proof or Lean formalization of $R_3^2(C_7) = 11$ was found (bounded search, not a claim of absolute priority). The lower-bound coloring specializes the paper's colored-$K_4$ template. See [PRIOR_ART.md](../PRIOR_ART.md#seven-cycle). |

## Proof overview

- **Lower bound ($R_3^2(C_7) \ge 11$, [SevenCycle/Lower.lean](SevenCycle/Lower.lean)):** To show 10 vertices are not enough, divide $K_{10}$ into one **apex** vertex and three 3-vertex groups labeled Red, Green, and Blue (specializing the colored-$K_4$ template of Allen et al.). Color edges as follows:
  - Every edge *inside* a group, and every edge from the apex to that group, gets that group's own color.
  - Every edge *between two different* groups gets the *third* color (for instance, Red–Green edges are Blue).

  Lean's kernel checks that every 7-cycle in this 3-coloring of $K_{10}$ undergoes at least 3 cyclic color changes.

- **Upper bound ($R_3^2(C_7) \le 11$, [SevenCycle/CheckedSeeds.lean](SevenCycle/CheckedSeeds.lean)):** Consider an arbitrary 3-coloring of $K_{11}$ and pick any vertex $v$. Its 10 incident edges are split among 3 colors, so by the pigeonhole principle at least $\lceil 10 / 3 \rceil = 4$ of them share a single color. Focus on the 10-vertex subgraph consisting of $v$, those 4 monochromatic neighbors, and 5 of the remaining vertices. Lean proves (`SevenCycle.star_forces_seven`) directly in the kernel that every way of 3-coloring the remaining edges forces a 7-cycle with at most 2 cyclic color changes.

## Check the proof

Run from this directory with Lean 4.36.0 (stdlib only; pure kernel check, no `native_decide`):

```sh
lake build
```

## References

- [Allen, Böttcher, Clemens, Hamann, Skokan, and Taraz, `arXiv:2607.03243v1`, Problem 22](https://arxiv.org/html/2607.03243v1#Thmtheorem22)
- [SevenCycle.lean](SevenCycle.lean)
- [Prior-art audit](../PRIOR_ART.md#seven-cycle)
