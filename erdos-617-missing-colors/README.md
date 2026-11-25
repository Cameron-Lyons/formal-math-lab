# Erdős Problem #617 (Erdos #617): Missing colors in cliques — Lean 4 proofs for r <= 10 and structural cases

**Status: the unrestricted Erdős–Gyárfás conjecture remains open.** Erdős and Gyárfás (1999) asked whether, for every integer $r \ge 3$, every $r$-edge-coloring of the complete graph $K_{r^2 + 1}$ contains a subset of $r + 1$ vertices whose induced edges omit at least one color. This Lean 4 project proves the conjecture for all **$3 \le r \le 10$**, proves it for arbitrary $r \ge 3$ under structural clique/degree conditions (including $r - 2$ disjoint monochromatic $K_r$'s in one color), and establishes tight structural restrictions on any hypothetical counterexample.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Erdős Problem #617** (`Erdos #617`, `erdosproblems.com/617`), Erdős–Gyárfás (`Erdos-Gyarfas`) balanced coloring / missing colors in cliques on $K_{r^2+1}$, `FormalConjectures/ErdosProblems/617.lean` |
| **Status** | **Solved for $3 \le r \le 10$ and structural families; unrestricted conjecture ($r \ge 11$) remains open.** |
| **Main Lean theorems** | `Erdos617.missing_of_at_most_ten_colors`, `Erdos617.missing_of_all_but_two_parallel_rows`, `Erdos617.missing_of_almost_parallel_full_cliques`, `Erdos617.missing_of_degree_excess`, `Erdos617.counterexample_rank_window` |
| **Verification** | `lake exe cache get && lake build` (Lean 4.35.0-rc2 + mathlib) |
| **Prior-art status** | Erdős and Gyárfás proved $r = 3, 4$; a separate formal verification covers $r = 5$. Priority for the $6 \le r \le 10$ cases and structural obstructions here is unverified. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-617-missing-colors-in-cliques). |

## Main Lean results

Import `Erdos617` to use the library; [Erdos617.lean](Erdos617.lean) documents all 29 modules and every proved counterexample obstruction in detail.

| Lean declaration (namespace `Erdos617`) | Result |
| --- | --- |
| `missing_of_at_most_ten_colors` | Proves the conjecture for every $r$-edge-coloring of $K_{r^2+1}$ with $3 \le r \le 10$. |
| `erdos_617.variants.r_eq_3` | Three-color case in the exact Formal Conjectures interface. |
| `missing_of_all_but_two_parallel_rows` | Proves the conjecture for every $r \ge 3$ when one color contains $r - 2$ vertex-disjoint copies of $K_r$. |
| `missing_of_almost_parallel_full_cliques` | Suffices to have $r - q$ vertex-disjoint copies of $K_r$ in one color whenever $1000(2q + 1)^2 < r$. |
| `missing_of_degree_excess`, `missing_of_regular_colors` | Proves the conjecture whenever one color has total degree excess `< r` above degree `r` (in particular, when one color class is regular or has max degree $\le r$). |
| `missing_of_line_subgraph_of_multiplicity_le_five` | Proves the conjecture for any $r$ if one color contains a spanning line graph of a loopless multigraph of multiplicity at most 5. |
| `counterexample_rank_window`, `counterexample_palette_descent` | Forces $r \ge 11$ and extracts a minimal obstruction of order $tr + 1$ with $5 \le t \le (r+1)/2$ ($t \ge 6$ for $r \ge 33$) and $r \le 1000t^2$, along with matching and palette-product bounds. |

## Build

Run from this directory with the pinned Lean **4.35.0-rc2** toolchain:

```sh
lake exe cache get
lake build
```

## References

* [Erdős Problems #617](https://www.erdosproblems.com/617)
* [Formal Conjectures `ErdosProblems/617.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/617.lean)
* [Erdős and Gyárfás (1999), *Split and balanced colorings of complete graphs*](https://doi.org/10.1016/S0012-365X(98)00323-9)
* [Prior 5-color formal verification (`RamazanKara/erdos-617-r5-formal-verification`)](https://github.com/RamazanKara/erdos-617-r5-formal-verification)
* [Dated prior-art audit](../PRIOR_ART.md#erdős-617-missing-colors-in-cliques)
