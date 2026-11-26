# Erdős Problem #1066 in higher dimensions

Let $g_d(n)$ be the largest $m$ such that every set of $n$ points in $\mathbb{R}^d$ with pairwise distances at least 1 contains $m$ points with pairwise distances strictly greater than 1. Pollack (1985) reports that Erdős asked for a proof or disproof of $g_d(n) > cn/d$. Our Lean 4 proof disproves this when $c$ must be independent of both $d$ and $n$: for $A = 2^m$, $d = 6A^2$, and $n = 4A^4$, we prove $g_d(n) \le 2A + 2$. The planar ($d = 2$) headline problem is not addressed.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #1066, higher-dimensional variant (`erdosproblems.com/1066`), `erdos_1066.variants.higher_dim` in `FormalConjectures/ErdosProblems/1066.lean` |
| Status | Variant refuted. The planar problem (the limit of $g_2(n)/n$) is not addressed. |
| Main theorems | `main : ¬ type_of% @Erdos1066.erdos_1066.variants.higher_dim`, `Sol1066.gDim_upper` in [Erdos1066.lean](Erdos1066.lean) |
| Written proof | [Erdos1066.md](Erdos1066.md), with the same lemma numbers as the Lean file |
| Verification | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos1066` (Lean 4.33.1 + Formal Conjectures) |
| Prior art | Checked 25 November 2026: follows quickly from D. de Caen's 2000 theorem on equiangular lines. We found no source drawing this conclusion, though experts may know it. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-1066-minimum-distances-in-higher-dimensions). |

## What Lean proves

| Lean declaration | Result |
| --- | --- |
| `main` | There is no $c > 0$ with $g_d(n) \ge cn/d$ for all $d \ge 1$ and all $n$. |
| `Sol1066.gDim_upper` | $g_d(n) \le 2A + 2$ for $A = 2^m$, $d = 6A^2$, and $n = 4A^4$. |

## Idea of the proof

Suppose we have $n$ vectors of squared length $2A^2 + A$ whose pairwise inner products are all $+A$ or $-A$. Only pairs with inner product $+A$ sit at the minimum distance. If $k$ of the vectors have pairwise inner products equal to $-A$, expanding $0 \le \lVert \sum w \rVert^2$ gives $k \le 2A + 2$. To finish, we construct $4A^4$ such vectors in $\mathbb{R}^{6A^2}$ using characters over the finite field with $2A^2$ elements.

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
* Full credits and unread sources are listed in [Erdos1066.lean](Erdos1066.lean) and [Erdos1066.md](Erdos1066.md#what-is-borrowed).
* [Prior-art audit](../PRIOR_ART.md#erdős-1066-minimum-distances-in-higher-dimensions)
