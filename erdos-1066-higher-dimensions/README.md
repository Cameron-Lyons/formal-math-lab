# Erdős Problem #1066 (Erdos #1066) in higher dimensions: no bound $g_d(n) \ge cn/d$ — Lean 4 disproof

**Status: the higher-dimensional question is answered "no"; the planar headline problem is untouched.** Let $g_d(n)$ be the largest $m$ such that every set of $n$ points of $\mathbb{R}^d$ with pairwise distances at least 1 contains $m$ points with pairwise distances greater than 1. Pollack (1985) reports that Erdős asked for a proof or disproof of $g_d(n) > cn/d$. This Lean 4 project disproves it, with $c$ independent of $d$ and $n$: for $A = 2^m$, $d = 6A^2$ and $n = 4A^4$ one has $g_d(n) \le 2A + 2$.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Erdős Problem #1066, higher-dimensional variant** (`Erdos #1066`, `erdosproblems.com/1066`), minimum-distance graphs, independence number, equiangular lines, `erdos_1066.variants.higher_dim` in `FormalConjectures/ErdosProblems/1066.lean` |
| **Status** | **Variant refuted.** The limit of $g_2(n)/n$ (the headline problem) is not addressed. |
| **Main Lean theorems** | `main : ¬ type_of% @Erdos1066.erdos_1066.variants.higher_dim`, `Sol1066.gDim_upper` in [Erdos1066.lean](Erdos1066.lean) |
| **Written proof** | [Erdos1066.md](Erdos1066.md), with the same lemma numbers as the Lean file |
| **Verification** | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos1066` (Lean 4.33.1 + Formal Conjectures) |
| **Prior-art status** | Checked **25 November 2026**: **a short corollary of D. de Caen's theorem on equiangular lines (2000).** No one was found who had drawn this conclusion, but it may well be known to experts. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-1066-minimum-distances-in-higher-dimensions). |

## What Lean proves

| Lean declaration | Result |
| --- | --- |
| `main` | There is no $c > 0$ with $g_d(n) \ge cn/d$ for all $d \ge 1$ and all $n$. |
| `Sol1066.gDim_upper` | $g_d(n) \le 2A + 2$ for $A = 2^m$, $d = 6A^2$, $n = 4A^4$. |

## Idea of the proof

Suppose $n$ vectors of squared length $2A^2 + A$ have all pairwise inner products $\pm A$. Only the pairs with $+A$ are at the minimum distance. If $k$ of the vectors have all pairwise inner products $-A$, then $0 \le \lVert \sum w \rVert^2$ gives $k \le 2A + 2$. It remains to write down $4A^4$ such vectors in dimension $6A^2$, which is done with characters over a field with $2A^2$ elements.

## Reproduce

Run from this directory with the pinned Lean **4.33.1** toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos1066
```

`lake build` checks the proof, that the type of `main` comes from the upstream statement (`type_of%`), and that `main` uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. `leanchecker` replays the module in the Lean kernel. The first build also compiles the part of Formal Conjectures that the statement imports, which takes a while. Formal Conjectures is a dependency pinned at commit `9097e2f9`; only its statements, definitions and proved lemmas are used, never the theorem it leaves as `sorry`.

The mathematics, the Lean proof and the literature searches are the work of AI agents. **No human has reviewed this project.**

## References and attribution

* R. Pollack, *Increasing the minimum distance of a set of points*, J. Combin. Theory Ser. A 40 (1985) 450.
* [Erdős Problems #1066](https://www.erdosproblems.com/1066) · [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/1066.lean#L126)
* **The vectors are not new.** D. de Caen, *Large equiangular sets of lines in Euclidean space*, Electron. J. Combin. 7 (2000) R55, has twice as many with the same inner products in one dimension fewer; with the norm argument above, the result follows at once. The construction here is a self-contained alternative; its form comes from the $\mathbb{Z}/4$ description of Kerdock codes.
* The norm argument is already used for one special system of lines by D. Ismailescu, S. Lee and T. Lee, [arXiv:2611.23767](https://arxiv.org/abs/2611.23767) (18 November 2026).
* Full credits, and the sources that could not be read, are in [Erdos1066.lean](Erdos1066.lean) and [Erdos1066.md](Erdos1066.md#what-is-borrowed).
* [Dated prior-art audit](../PRIOR_ART.md#erdős-1066-minimum-distances-in-higher-dimensions)
