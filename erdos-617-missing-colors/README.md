# Erdős #617 — Missing colors in cliques

Erdős and Gyárfás asked whether, for every $r\ge 3$, every $r$-edge-coloring of $K_{r^2+1}$ has $r+1$ vertices whose edges omit a color. The unrestricted conjecture remains open. [Problem statement](https://www.erdosproblems.com/617) · [Upstream Lean statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/617.lean)

| Lean declaration | Result |
| --- | --- |
| `Erdos617.missing_of_at_most_ten_colors` | Gives the missing color for every coloring with $3\le r\le 10$. |
| `Erdos617.missing_of_all_but_two_parallel_rows` | Gives the missing color for every $r\ge3$ when one color contains $r-2$ vertex-disjoint copies of $K_r$. |
| `Erdos617.missing_of_almost_parallel_full_cliques` | It suffices to have $r-q$ such cliques whenever $1000(2q+1)^2<r$. |

Import `Erdos617` to use the library. The entry point also summarizes the restrictions proved for hypothetical counterexamples. [Library overview](Erdos617.lean)

## Build

Run from this directory with the pinned Lean toolchain.

```sh
lake exe cache get
lake build
```
