# Erdős Problem #344: the $\sqrt{2N}$ variant

Suppose a set $A \subseteq \mathbb{N}$ of natural numbers contains at least $\sqrt{2N}$ elements in $\{1, \dots, N\}$ for every sufficiently large $N$. If we form all **subset sums** of $A$—that is, all sums of finitely many distinct elements of $A$—must they contain an infinite arithmetic progression $x, x+d, x+2d, \dots$?

This project gives a machine-checked Lean 4 proof that the answer is **yes**, settling the $\sqrt{2N}$ variant asked by Folkman in 1966. The headline problem of Erdős #344 replaces $\sqrt{2}$ by an arbitrary absolute constant and was proved by Szemerédi and Vu (2006; see also Chen 2003). No constant strictly below $\sqrt{2}$ can work: Erdős (1961/62) constructed sets with at least $c\sqrt{N}$ elements up to every large $N$ (for any $c < \sqrt{2}$) whose subset sums have arbitrarily long gaps.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #344, $\sqrt{2N}$ variant (`erdosproblems.com/344`), Folkman (1966), `erdos_344.variants.sqrt_two` in `FormalConjectures/ErdosProblems/344.lean` |
| Status | Variant proved. The exact threshold is not determined ($\sqrt{2N}$ is not sharp; see [Erdos344.md](Erdos344.md#two-remarks-not-part-of-the-lean-file)). |
| Main theorem | `main : type_of% @Erdos344.erdos_344.variants.sqrt_two` in [Erdos344.lean](Erdos344.lean) |
| Written proof | [Erdos344.md](Erdos344.md), with the same lemma numbers as the Lean file |
| Verification | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos344` (Lean 4.33.1 + Formal Conjectures) |
| Prior art | Checked 25 November 2026: two limited searches found no earlier proof of the $\sqrt{2N}$ statement, though much of the argument is close to published work. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-344-the-square-root-of-2n-variant). |

## How the proof works

List the elements of $A$ in increasing order as $a_0 < a_1 < \cdots$. The density bound $|A \cap \{1, \dots, N\}| \ge \sqrt{2N}$ translates directly into a quadratic growth ceiling: $a_m \le m^2/2 + 1$ for all large $m$.

Call a subset of $A$ **good** if every element exceeds the sum of all smaller elements in that subset by at most a fixed constant (like the powers of $2$, where $2^m = 1 + \sum_{i<m} 2^i$). The subset sums of an infinite good subset have **bounded gaps** (they are *syndetic*), and the same holds for the multiples of any fixed $d \ge 1$ among those subset sums. Because of this, it is enough to split $A$ into a good subset $C$ and a disjoint remainder $J$ whose subset sums contain *arbitrarily long finite* arithmetic progressions, all sharing one fixed common difference $d$; adding the multiples of $d$ from $C$ glues a single finite progression into an infinite one.

The proof splits on whether small consecutive gaps $a_{i+1} - a_i \le 10$ appear infinitely often:

* **Case 1 (a small gap $d \le 10$ repeats infinitely often):** Choose a geometrically sparse sequence of disjoint pairs $\{a_{p_r}, a_{p_r+1}\}$ with difference $d$. Picking one element from each of $L$ pairs immediately gives a progression of length $L+1$ with difference $d$. Unless $a_{i+1} = a_i + 1$ eventually (which already yields an infinite progression in $A$ itself), we have $a_i \ge i + 4$ eventually; the sum of the remaining elements before $a_m$ is at least $m^2/2 - O(1) \ge a_m - O(1)$, so the complement is good. **This is the only place in the proof where the constant $\sqrt{2}$ is used.**
* **Case 2 ($a_{i+1} \ge a_i + 11$ for all large $i$):** Here $a_k$ grows at least linearly at rate $10k$, fast enough that all four index residue classes modulo $4$ are simultaneously good. Two classes give bounded-gap sumsets $X$ and $Y$, the fourth is saved for final gluing, and the third feeds a multiscale pigeonhole-and-saturation argument that produces arbitrarily long progressions with one fixed difference $d$ inside $X + Y + \Sigma(b)$.

For the full self-contained exposition—including two remarks on Folkman's boundary $\theta = 1/2$ and Erdős's $c < \sqrt{2}$ counterexample—see [Erdos344.md](Erdos344.md).

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos344
```

**Trust boundary and verification notes:**

* `lake build` checks the proof, confirms that `main` matches the upstream statement type (via `type_of%`), and verifies that `main` uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
* `leanchecker` replays the compiled module independently in the Lean kernel.
* The first build also compiles the imported part of Formal Conjectures (pinned at commit `9097e2f9`). We use only its statements, definitions, and proved lemmas, never any theorem left as `sorry`.
* The mathematics, Lean proof, and literature searches were produced by AI agents. No human has reviewed this project.

## References and attribution

* [Erdős Problems #344](https://www.erdosproblems.com/344) and [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/344.lean#L71)
* J. Folkman, [Canad. J. Math. 18 (1966) 643-655](https://doi.org/10.4153/CJM-1966-065-2) (p. 655); P. Erdős, [Acta Arith. 7 (1961/62) 345-354](https://users.renyi.hu/~p_erdos/1961-18.pdf); E. Szemerédi and V. H. Vu, [Ann. of Math. 163 (2006) 1-35](https://doi.org/10.4007/annals.2006.163.1). A Lean proof of the headline problem with a large constant is in [plby/lean-proofs](https://github.com/plby/lean-proofs).
* Case 1 is close to Lemma 6.1 of S. Fan, [arXiv:2607.14071](https://arxiv.org/abs/2607.14071). Case 2 follows the plan of V. Bergelson and D. Simmons, [arXiv:1507.02208](https://arxiv.org/abs/1507.02208), whose theorem appears to give it under a gcd condition.
* Two remarks in print conflict or may conflict with the theorem (Hegyvári 2000, Chen 2003). Both are discussed, with full credits, in [Erdos344.lean](Erdos344.lean).
* [Prior-art audit](../PRIOR_ART.md#erdős-344-the-square-root-of-2n-variant)
