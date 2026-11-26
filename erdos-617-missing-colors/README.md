# Erdős Problem #617: missing colors in cliques

Erdős and Gyárfás (1999) asked whether every $r$-edge-coloring of $K_{r^2 + 1}$ (for $r \ge 3$) has $r + 1$ vertices whose induced edges omit at least one color. The general conjecture is still open.

This Lean 4 project proves the conjecture for $3 \le r \le 10$, settles all $r \ge 3$ under several clique or degree assumptions (including $r - 2$ disjoint monochromatic copies of $K_r$ in one color), and restricts the structure of any counterexample.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #617 (`erdosproblems.com/617`), Erdős-Gyárfás balanced coloring on $K_{r^2+1}$, `FormalConjectures/ErdosProblems/617.lean` |
| Status | Proved for $3 \le r \le 10$ and several structural families; $r \ge 11$ is still open. |
| Main theorems | `Erdos617.missing_of_at_most_ten_colors`, `Erdos617.missing_of_all_but_two_parallel_rows`, `Erdos617.missing_of_almost_parallel_full_cliques`, `Erdos617.missing_of_degree_excess`, `Erdos617.counterexample_rank_window` |
| Verification | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib) |
| Prior art | Erdős and Gyárfás proved $r = 3, 4$; a separate formal verification covers $r = 5$. Priority for $6 \le r \le 10$ and the structural obstructions is unverified. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-617-missing-colors-in-cliques). |

## Main Lean results

Import `Erdos617` to use the library. [Erdos617.lean](Erdos617.lean) lists all 29 modules and the counterexample obstructions.

| Lean declaration (namespace `Erdos617`) | Result |
| --- | --- |
| `missing_of_at_most_ten_colors` | Proves the conjecture for every $r$-edge-coloring of $K_{r^2+1}$ with $3 \le r \le 10$. |
| `erdos_617.variants.r_eq_3` | Three-color case in the Formal Conjectures interface. |
| `missing_of_all_but_two_parallel_rows` | Proves the conjecture for every $r \ge 3$ when one color contains $r - 2$ vertex-disjoint copies of $K_r$. |
| `missing_of_almost_parallel_full_cliques` | Proves the conjecture whenever one color has $r - q$ vertex-disjoint copies of $K_r$ and $1000(2q + 1)^2 < r$. |
| `missing_of_degree_excess`, `missing_of_regular_colors` | Proves the conjecture whenever one color has total degree excess `< r` above degree `r` (in particular, when one color class is regular or has max degree $\le r$). |
| `missing_of_line_subgraph_of_multiplicity_le_five` | Proves the conjecture for any $r$ if one color contains a spanning line graph of a loopless multigraph of multiplicity at most 5. |
| `counterexample_rank_window`, `counterexample_palette_descent` | Forces $r \ge 11$ for any counterexample and extracts a minimal obstruction of order $tr + 1$ with $5 \le t \le (r+1)/2$ ($t \ge 6$ for $r \ge 33$) and $r \le 1000t^2$, plus matching and palette-product bounds. |

## Build

Run from this directory with the pinned Lean 4.36.0 toolchain:

```sh
lake exe cache get
lake build
```

## References

* [Erdős Problems #617](https://www.erdosproblems.com/617)
* [Formal Conjectures `ErdosProblems/617.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/617.lean)
* [Erdős and Gyárfás (1999), *Split and balanced colorings of complete graphs*](https://doi.org/10.1016/S0012-365X(98)00323-9)
* [Prior 5-color formal verification (`RamazanKara/erdos-617-r5-formal-verification`)](https://github.com/RamazanKara/erdos-617-r5-formal-verification)
* [Prior-art audit](../PRIOR_ART.md#erdős-617-missing-colors-in-cliques)
