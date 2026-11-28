# Erdős Problem #1066 in higher dimensions

Imagine placing $n$ points in $d$-dimensional Euclidean space so that no two are closer than distance $1$ (equivalently, packing $n$ non-overlapping spheres of diameter $1$). Some pairs of points may sit at distance *exactly* $1$, and we want to pick as large a subset as possible in which *no* two points are at distance $1$ — every remaining pairwise distance is strictly greater than $1$.

Let $g_d(n)$ denote the largest $m$ such that every set of $n$ points in $\mathbb{R}^d$ with pairwise distances at least $1$ contains $m$ points with pairwise distances strictly greater than $1$. Pollack (1985) reports that Erdős asked for a proof or disproof of $g_d(n) > cn/d$. Our Lean 4 proof disproves this when $c > 0$ must be an absolute constant independent of both $d$ and $n$: for every $A = 2^m$, in dimension $d = 6A^2$ with $n = 4A^4$ points, we construct a configuration giving $g_d(n) \le 2A + 2$ (which drops below $cn/d = \frac{2}{3}cA^2$ for large $m$). The planar ($d = 2$) headline problem is not addressed.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #1066, higher-dimensional variant (`erdosproblems.com/1066`), `erdos_1066.variants.higher_dim` in `FormalConjectures/ErdosProblems/1066.lean` |
| Status | Variant refuted. The planar problem (the limit of $g_2(n)/n$) is not addressed. |
| Main theorems | `main : ¬ type_of% @Erdos1066.erdos_1066.variants.higher_dim`, `Sol1066.gDim_upper` in [Erdos1066.lean](Erdos1066.lean) |
| Verification | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos1066` (Lean 4.33.1 + Formal Conjectures) |
| Prior art | Checked 25 November 2026: follows quickly from D. de Caen's 2000 theorem on equiangular lines. We found no source drawing this conclusion, though experts may know it. |

## What Lean proves

| Lean declaration | Result |
| --- | --- |
| `main` | There is no $c > 0$ with $g_d(n) \ge cn/d$ for all $d \ge 1$ and all $n$. |
| `Sol1066.gDim_upper` | $g_d(n) \le 2A + 2$ for $A = 2^m$, $d = 6A^2$, and $n = 4A^4$. |

## Idea of the proof

The refutation combines a two-line norm bound with a dense family of vectors having only two pairwise inner products (a scaled system of *equiangular lines*, meaning lines through the origin that all meet at the same acute angle):

1. **From two inner products to a sharp cap on kept points.** Suppose we have $n$ vectors of squared length $2A^2 + A$ whose pairwise inner products are all either $+A$ or $-A$. Because $\lVert u - v \rVert^2 = \lVert u \rVert^2 + \lVert v \rVert^2 - 2\langle u, v \rangle$, only pairs with inner product $+A$ sit at the minimum distance (which rescales to $1$), while pairs with inner product $-A$ sit strictly farther apart. If $k$ of the points have all pairwise distances strictly greater than $1$, their $k$ vectors must all have pairwise inner product $-A$. Expanding the non-negative squared norm $0 \le \lVert \sum w \rVert^2 = k(2A^2 + A) - k(k - 1)A$ immediately forces $k \le 2A + 2$.
2. **Packing $4A^4$ such vectors into $\mathbb{R}^{6A^2}$.** To beat $cn/d$, we need quadratically many vectors ($n \asymp d^2$) so that $n/d$ grows like $A^2$ while $k$ grows only like $A$. We construct $4A^4$ vectors with these exact lengths and inner products in $\mathbb{R}^{6A^2}$ using characters (homomorphisms to the complex unit circle) on a twisted product $F \times F$ over the finite field $F$ with $2A^2$ elements, plus an extra real coordinate slot that adjusts orthogonal pairs from $0$ to $+A$.

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos1066
```

`lake build` checks the proof, confirms that `main` matches the upstream statement type (via `type_of%`), and verifies that `main` uses only `propext`, `Classical.choice`, and `Quot.sound`. `leanchecker` replays the module in the Lean kernel. The first build also compiles the imported part of Formal Conjectures (pinned at commit `9097e2f9`). We use only its statements, definitions, and proved lemmas, never any theorem left as `sorry`.

The mathematics, Lean proof, and literature searches were produced by AI agents. No human has reviewed this project.

## References and attribution

* R. Pollack, *Increasing the minimum distance of a set of points*, J. Combin. Theory Ser. A 40 (1985) 450.
* [Erdős Problems #1066](https://www.erdosproblems.com/1066) and [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/1066.lean#L126)
* The vectors are not new: D. de Caen, *Large equiangular sets of lines in Euclidean space*, Electron. J. Combin. 7 (2000) R55, constructs twice as many vectors with the same inner products in one fewer dimension. Combined with the norm argument above, that already yields the refutation. Our construction is a self-contained alternative based on the $\mathbb{Z}/4$ description of Kerdock codes.
* The same norm argument is used for one special system of lines by D. Ismailescu, S. Lee, and T. Lee, [arXiv:2611.23767](https://arxiv.org/abs/2611.23767) (18 November 2026).
* Full credits and unread sources are listed in [Erdos1066.lean](Erdos1066.lean).
