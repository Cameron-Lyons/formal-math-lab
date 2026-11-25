# Erdős Problem #344: the $\sqrt{2N}$ variant

If $A \subseteq \mathbb{N}$ has at least $\sqrt{2N}$ elements in $\{1, \dots, N\}$ for all large $N$, then the sums of finitely many distinct elements of $A$ contain an infinite arithmetic progression. The Lean 4 proof here establishes this $\sqrt{2N}$ variant (asked by Folkman in 1966). The headline problem replaces $\sqrt 2$ by an arbitrary absolute constant and was proved by Szemerédi and Vu (2006; see also Chen 2003). No constant below $\sqrt 2$ suffices (Erdős 1961/62).

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #344, $\sqrt{2N}$ variant (`erdosproblems.com/344`), Folkman (1966), `erdos_344.variants.sqrt_two` in `FormalConjectures/ErdosProblems/344.lean` |
| Status | Variant proved. The exact threshold is not determined ($\sqrt{2N}$ is not sharp; see [Erdos344.md](Erdos344.md#two-remarks-not-part-of-the-lean-file)). |
| Main theorem | `main : type_of% @Erdos344.erdos_344.variants.sqrt_two` in [Erdos344.lean](Erdos344.lean) |
| Written proof | [Erdos344.md](Erdos344.md), with the same lemma numbers as the Lean file |
| Verification | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos344` (Lean 4.33.1 + Formal Conjectures) |
| Prior art | Checked 25 November 2026: no earlier proof of the $\sqrt{2N}$ statement located in two limited searches, though much of the argument is close to published work. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-344-the-square-root-of-2n-variant). |

## Idea of the proof

List $A$ as $a_0 < a_1 < \cdots$; the hypothesis gives $a_m \le m^2/2 + 1$ for large $m$. Call a subset of $A$ *good* if each of its elements exceeds the sum of the smaller ones by at most a constant. The subset sums of a good subset have bounded gaps, so it suffices to find arbitrarily long progressions with one fixed difference outside a good subset.

* If some difference $a_{i+1} - a_i = d$ occurs infinitely often, choose one element from each of a sparse family of such pairs. The rest is good, and this is the only place where the constant $\sqrt 2$ is used.
* Otherwise the index classes modulo 4 are good, and a pigeonhole argument at geometric scales produces the progressions.

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos344
```

`lake build` checks the proof, verifies that the type of `main` matches the upstream statement (`type_of%`), and confirms that `main` uses only `propext`, `Classical.choice`, and `Quot.sound`. `leanchecker` replays the module in the Lean kernel. The first build also compiles the part of Formal Conjectures imported by the statement. Formal Conjectures is pinned at commit `9097e2f9`; only its statements, definitions, and proved lemmas are used, never the theorem it leaves as `sorry`.

The mathematics, Lean proof, and literature searches are the work of AI agents. No human has reviewed this project.

## References and attribution

* [Erdős Problems #344](https://www.erdosproblems.com/344) and [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/344.lean#L71)
* J. Folkman, [Canad. J. Math. 18 (1966) 643-655](https://doi.org/10.4153/CJM-1966-065-2) (p. 655); P. Erdős, [Acta Arith. 7 (1961/62) 345-354](https://users.renyi.hu/~p_erdos/1961-18.pdf); E. Szemerédi and V. H. Vu, [Ann. of Math. 163 (2006) 1-35](https://doi.org/10.4007/annals.2006.163.1). A Lean proof of the headline problem with a large constant is in [plby/lean-proofs](https://github.com/plby/lean-proofs).
* The first case is close to Lemma 6.1 of S. Fan, [arXiv:2607.14071](https://arxiv.org/abs/2607.14071). The plan of the second is that of V. Bergelson and D. Simmons, [arXiv:1507.02208](https://arxiv.org/abs/1507.02208), whose theorem appears to give it under a condition on gcds.
* Two remarks in print conflict or may conflict with the theorem (Hegyvári 2000, Chen 2003). They are discussed, with full credits, in [Erdos344.lean](Erdos344.lean).
* [Prior-art audit](../PRIOR_ART.md#erdős-344-the-square-root-of-2n-variant)
