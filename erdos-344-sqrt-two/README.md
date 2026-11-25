# Erdős Problem #344 (Erdos #344), the $\sqrt{2N}$ variant: subcomplete sets — Lean 4 proof

**Status: the $\sqrt{2N}$ variant is proved; the headline problem was solved long ago.** If $A \subseteq \mathbb{N}$ has at least $\sqrt{2N}$ elements in $\{1, \dots, N\}$ for all large $N$, then the sums of finitely many distinct elements of $A$ contain an infinite arithmetic progression. The headline problem asks for this with some absolute constant in place of $\sqrt 2$, and is due to Szemerédi and Vu (2006; see also Chen 2003). No constant below $\sqrt 2$ would do (Erdős 1961/62).

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Erdős Problem #344, $\sqrt{2N}$ variant** (`Erdos #344`, `erdosproblems.com/344`), subcomplete sets, subset sums, Folkman (1966), `erdos_344.variants.sqrt_two` in `FormalConjectures/ErdosProblems/344.lean` |
| **Status** | **Variant proved.** The exact threshold is not determined: $\sqrt{2N}$ is not it (see the remarks in [Erdos344.md](Erdos344.md#two-remarks-not-part-of-the-lean-file)). |
| **Main Lean theorems** | `main : type_of% @Erdos344.erdos_344.variants.sqrt_two` in [Erdos344.lean](Erdos344.lean) |
| **Written proof** | [Erdos344.md](Erdos344.md), with the same lemma numbers as the Lean file |
| **Verification** | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos344` (Lean 4.33.1 + Formal Conjectures) |
| **Prior-art status** | Checked **25 November 2026**: no earlier proof of the $\sqrt{2N}$ statement located in two limited searches. Much of it is close to published work. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-344-the-square-root-of-2n-variant). |

## Idea of the proof

List $A$ as $a_0 < a_1 < \cdots$; the hypothesis gives $a_m \le m^2/2 + 1$ for large $m$. Call a part of $A$ *good* if each of its elements exceeds the sum of the smaller ones by at most a constant. The subset sums of a good part have bounded gaps, so it is enough to find arbitrarily long progressions with one fixed difference outside a good part.

* If some difference $a_{i+1} - a_i = d$ occurs infinitely often, choose one element from each of a very sparse family of such pairs. The rest is good, and this is the only place where the constant $\sqrt 2$ is used.
* Otherwise the index classes modulo 4 are good, and a pigeonhole argument at geometric scales finds the progressions.

## Reproduce

Run from this directory with the pinned Lean **4.33.1** toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos344
```

`lake build` checks the proof, that the type of `main` comes from the upstream statement (`type_of%`), and that `main` uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. `leanchecker` replays the module in the Lean kernel. The first build also compiles the part of Formal Conjectures that the statement imports, which takes a while. Formal Conjectures is a dependency pinned at commit `9097e2f9`; only its statements, definitions and proved lemmas are used, never the theorem it leaves as `sorry`.

The mathematics, the Lean proof and the literature searches are the work of AI agents. **No human has reviewed this project.**

## References and attribution

* [Erdős Problems #344](https://www.erdosproblems.com/344) · [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/344.lean#L71)
* J. Folkman, [Canad. J. Math. 18 (1966) 643–655](https://doi.org/10.4153/CJM-1966-065-2), is the source of the question (p. 655); P. Erdős, [Acta Arith. 7 (1961/62) 345–354](https://users.renyi.hu/~p_erdos/1961-18.pdf); E. Szemerédi and V. H. Vu, [Ann. of Math. 163 (2006) 1–35](https://doi.org/10.4007/annals.2006.163.1). A Lean proof of the headline problem with a large constant is in [plby/lean-proofs](https://github.com/plby/lean-proofs).
* The first case is close to Lemma 6.1 of S. Fan, [arXiv:2607.14071](https://arxiv.org/abs/2607.14071). The plan of the second is that of V. Bergelson and D. Simmons, [arXiv:1507.02208](https://arxiv.org/abs/1507.02208), whose theorem appears to give it under a condition on gcds.
* Two remarks in print conflict or may conflict with the theorem (Hegyvári 2000, Chen 2003). They are discussed, with the full credits, in [Erdos344.lean](Erdos344.lean).
* [Dated prior-art audit](../PRIOR_ART.md#erdős-344-the-square-root-of-2n-variant)
