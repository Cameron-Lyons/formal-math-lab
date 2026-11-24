# Written on the Wall II, Graph Conjecture 133

For a finite simple connected graph $G$, let $p$ be the number of vertices in a longest induced path, $r$ its radius, and $k=\lfloor l(G)\rfloor$, where $l(G)$ is the average of the independence numbers of the open neighborhoods. The floored conjecture asks for $p\ge r+k$ when $G$ contains no four-cycle, and $p\ge r+1$ when it contains any four-cycle, including one with a chord. [Graffiti.pc catalogue, Conjecture 133](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)

This project studies the earlier, floored Lean formulation. In September 2026 Formal Conjectures interpreted the catalogue’s brackets as grouping and changed its declaration to use the unrounded $l(G)$. The two bounds differ when $G$ is $C_4$-free and $l(G)$ is nonintegral. [Upstream correction](https://github.com/google-deepmind/formal-conjectures/commit/5faef0c4dc3d226f8f9a9fc8f581b6221283eb6e) · [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/WrittenOnTheWallII/GraphConjecture133.lean#L46-L54)

## What Lean proves

The floored inequality holds for **every graph on at most 29 vertices** and **every graph with $k\le4$**, under the assumptions above. It also holds for every connected bipartite graph, regular graph, and graph of diameter at most two. The unrestricted problem remains open in this project. Import `Wall133` to use the following declarations. [Library entry point](Wall133.lean)

| Lean declaration in `Wall133` | Result |
| --- | --- |
| `floored_of_order_le_29` | The inequality holds for all orders through 29. |
| `floored_of_floor_le_four` | The inequality holds for $k\le4$ at every order and radius. |
| `floored_of_bipartite`, `floored_of_regular`, `floored_of_diameter_le_two` | Each class satisfies the inequality for all $k$. |
| `eight_le_path_of_five_le_average` | Every $C_4$-free graph with $l(G)\ge5$ has an induced path on at least eight vertices. |
| `remaining_fifth_band`, `order_of_counterexample_radius_ge_four` | A counterexample at $k=5$ has girth three or five. Its $(r,p)$ is $(4,8)$ with at least 30 vertices or $(5,9)$ with at least 31 vertices. |

The order bound comes from counting neighborhoods along a shortest path. A counterexample must have a vertex whose neighborhood independence falls below $k$. Its contribution makes the sum of squared neighborhood independence numbers strictly greater than $k^2|V(G)|$. The local counts then force $|V(G)|\ge k^2+r$, with one extra vertex when $r\ge4$. [Counting argument](Wall133/OrderBound.lean) · [Strict bound](Wall133/StrictOrderBound.lean)

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain. Lake builds all 110 project modules, including the finite path certificates. The final command replays their declarations in the Lean kernel.

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker -v Wall133
```

The radius estimate $p\ge 2r-1$ is Theorem 2.2 of Erdős, Saks and Sós, who credit the proof to Fan Chung. This package adapts KitaKen1’s Lean formalization to the pinned graph definitions and retains the Apache-2.0 license. [Paper](https://real.mtak.hu/110576/1/1-s2.0-0095895686900286-main.pdf#page=4) · [Original Lean proof](https://github.com/KitaKen1/wowii-graph-conjecture-31-lean/blob/a948e9fc07e11b786aee8dadb1376b4d938454d6/lean/GraphConjecture31.lean) · [Adaptation](Wall133/Chung.lean) · [License](LICENSE)
