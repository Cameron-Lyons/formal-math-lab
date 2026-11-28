# Written on the Wall II, Graph Conjecture 133 (floored formulation)

For a finite simple connected graph $G$, consider three structural invariants:
- **$p(G)$ (longest induced path):** the maximum number of vertices in a path in $G$ with no extra "shortcut" edges (chords) between non-consecutive vertices of the path.
- **$r(G)$ (radius):** the smallest possible worst-case distance from a chosen center vertex to every other vertex in $G$.
- **$l(G)$ (average neighborhood independence number):** for each vertex $v$, take its *open neighborhood* $N(v)$ (all neighbors of $v$, excluding $v$ itself) and find the largest set of pairwise non-adjacent vertices inside $N(v)$—its neighborhood independence number $\alpha(N(v))$. Averaging $\alpha(N(v))$ over all vertices $v \in V(G)$ yields $l(G)$, and we write $k = \lfloor l(G) \rfloor$.

The floored formulation of **Written on the Wall II, Graph Conjecture 133** (`WOWII #133`, from Ermelinda DeLaViña's Graffiti.pc catalogue) asks whether every finite simple connected graph $G$ satisfies:
- $p(G) \ge r(G) + \lfloor l(G) \rfloor$ when $G$ is **$C_4$-free** (contains no 4-cycle), and
- $p(G) \ge r(G) + 1$ when $G$ contains a 4-cycle (including a chorded 4-cycle).

*(Historical note on formulations: in September 2026, Formal Conjectures reinterpreted the brackets in the original source text as grouping rather than floor and changed its statement to the unrounded bound $p \ge r + l(G)$, which is strictly stronger when $G$ is $C_4$-free and $l(G)$ is non-integer. The Lean 4 proofs here address the earlier floored formulation: [upstream change](https://github.com/google-deepmind/formal-conjectures/commit/5faef0c4dc3d226f8f9a9fc8f581b6221283eb6e), [pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/WrittenOnTheWallII/GraphConjecture133.lean#L46-L54). The general conjecture remains open.)*

| Field | Summary |
| --- | --- |
| Problem | Written on the Wall II, Graph Conjecture 133 (`WOWII #133`, `Graffiti.pc #133`), floored formulation $p \ge r + \lfloor l(G) \rfloor$ |
| Status | Proved for all connected graphs with $\lvert V(G) \rvert \le 29$, all graphs with $\lfloor l(G) \rfloor \le 4$, and all connected bipartite, regular, or diameter $\le 2$ graphs. The first open case has $k = 5$, girth 3 or 5, and at least 30 vertices. |
| Main theorems | `Wall133.floored_of_order_le_29`, `floored_of_floor_le_four`, `floored_of_bipartite`, `floored_of_regular`, `floored_of_diameter_le_two`, `eight_le_path_of_five_le_average`, `remaining_fifth_band` in [Wall133.lean](Wall133.lean) |
| Verification | `lake exe cache get && lake build && lake env leanchecker --fresh Wall133` (Lean and mathlib 4.36.0; all 98 modules kernel-verified) |
| Prior art | Checked 24 November 2026: Haoyu Chen previously treated $C_4$-containing graphs and floors through 2 (with restrictions at 3), and Kuber Mehta treated special classes; priority of the stronger local bounds ($\le 29$ vertices, floor $\le 4$, bipartite/regular) is unverified. |

## What Lean proves

Import `Wall133` to access all declarations ([Wall133.lean](Wall133.lean)):

| Lean declaration (namespace `Wall133`) | Result |
| --- | --- |
| `floored_of_order_le_29` | The floored inequality holds for every connected graph on at most 29 vertices. |
| `floored_of_floor_le_four` | The floored inequality holds for every connected graph with $k = \lfloor l(G) \rfloor \le 4$, regardless of order or radius. |
| `floored_of_bipartite`, `floored_of_regular`, `floored_of_diameter_le_two` | Holds for every connected bipartite graph, regular graph, and graph of diameter at most 2, for all $k$. |
| `eight_le_path_of_five_le_average` | Every connected $C_4$-free graph with $l(G) \ge 5$ contains an induced path on at least 8 vertices. |
| `remaining_fifth_band`, `order_of_counterexample_radius_ge_four` | Any counterexample at $k = 5$ has **girth** (shortest cycle length) 3 or 5, and satisfies either $(r, p) = (4, 8)$ with $\lvert V(G) \rvert \ge 30$ or $(r, p) = (5, 9)$ with $\lvert V(G) \rvert \ge 31$. |

### How the order bound works

In a $C_4$-free graph, two non-adjacent vertices can share at most one common neighbor (two common neighbors would immediately create a 4-cycle), strongly restricting how open neighborhoods overlap.

For any hypothetical counterexample to $p(G) \ge r(G) + k$, Lean shows that at least one vertex must have neighborhood independence number strictly below $k$. Because the *average* neighborhood independence number is still at least $k$, strict variance (Cauchy–Schwarz) pushes the sum of squared neighborhood independence numbers strictly above $k^2 |V(G)|$. Counting neighborhoods along a shortest path turns that strict surplus into the vertex lower bound $|V(G)| \ge k^2 + r$—and forces one extra vertex whenever $r \ge 4$ (yielding $5^2 + 4 + 1 = 30$ at $k = 5, r = 4$ and $5^2 + 5 + 1 = 31$ at $k = 5, r = 5$; [Wall133/OrderBound.lean](Wall133/OrderBound.lean), [Wall133/StrictOrderBound.lean](Wall133/StrictOrderBound.lean)).

## Reproduce

Run from this directory with the pinned Lean 4.36.0 toolchain. Lake builds all 98 modules (including the finite path certificates), and `leanchecker` replays them completely inside Lean's kernel:

```sh
lake exe cache get
lake build
lake env leanchecker --fresh Wall133
```

## References and attribution

- [DeLaViña's Graffiti.pc / Written on the Wall II catalogue, Conjecture 133](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)
- [Haoyu Chen's report (`10.5281/zenodo.22054835`)](https://doi.org/10.5281/zenodo.22054835) and [Kuber Mehta's regular/low-average notes](https://github.com/Kuberwastaken/c5-k4/blob/f0f912c17bde0aa1b1f4b59845cf018eea696452/results/expansion/method_v09_133_regular.md)
- The radius estimate $p \ge 2r - 1$ is Theorem 2.2 of Erdős, Saks, and Sós (proof credited to Fan Chung, [paper](https://real.mtak.hu/110576/1/1-s2.0-0095895686900286-main.pdf#page=4)). This package adapts KitaKen1's Lean formalization ([original Lean proof](https://github.com/KitaKen1/wowii-graph-conjecture-31-lean/blob/a948e9fc07e11b786aee8dadb1376b4d938454d6/lean/GraphConjecture31.lean), [Wall133/Chung.lean](Wall133/Chung.lean)) and keeps the [Apache-2.0 license](LICENSE).
