# Erdős Problem #387: Schinzel's conjecture for all large $k$

If $k$ is large enough and not a prime power, there is an integer $n$ such that none of $n, n-1, \dots, n-k+1$ divides $\binom{n}{k}$. Schinzel (1958) proved that no such $n$ exists when $k$ is a prime power, and asked in Colloq. Math. Problem P 217 whether this failure happens for infinitely many other $k$, expecting the answer to be no. Our Lean 4 proof settles Schinzel's conjecture for all sufficiently large $k$. Because the threshold is not explicit, nothing is proved for any specific $k$. The headline problem is a separate question answered elsewhere.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #387, Schinzel variant (`erdosproblems.com/387`), Colloq. Math. P 217, `erdos_387.variants.schinzel` in `FormalConjectures/ErdosProblems/387.lean` |
| Status | Eventual form proved. The explicit form (every non-prime-power $k \ge 35$) remains open. |
| Main theorem | `main : type_of% @Erdos387.erdos_387.variants.schinzel` in [Erdos387.lean](Erdos387.lean) |
| Written proof | [Erdos387.md](Erdos387.md), with the same lemma numbers as the Lean file |
| Verification | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos387` (Lean 4.33.1 + Formal Conjectures) |
| Prior art | Checked 25 November 2026: no earlier proof of the all-large-$k$ statement was found. Erdős wrote in 1985 that Lacampagne and Selfridge could probably prove it, though no paper was found. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-387-schinzels-conjecture-for-large-k). |

## Idea of the proof

By Kummer's theorem and the Chinese remainder theorem, it is enough to choose for each prime $p \le k$ a residue class $a_p$ with $k \bmod p < a_p \le p$ so that these classes cover $1, \dots, k$ (Schinzel). Start with class zero for every prime. Move the largest prime factor of $k$ to class 1, and move one auxiliary prime to a class that contains many large primes.

We then cover the remaining uncovered numbers $n$ one by one, in order of their level $\min(n, k-n)$, assigning each a fresh prime. A parity argument shows that moving a prime uncovers only numbers at higher levels. Chebyshev's bounds and Størmer's theorem ensure that fresh primes do not run out, and the few numbers left at the end are covered by large primes.

The Lean proof is about 2,400 lines long.

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos387
```

`lake build` checks the proof, confirms that `main` matches the upstream statement type (via `type_of%`), and verifies that `main` uses only `propext`, `Classical.choice`, and `Quot.sound`. `leanchecker` replays the module in the Lean kernel. The first build also compiles the imported part of Formal Conjectures (pinned at commit `9097e2f9`). We use only its statements, definitions, and proved lemmas, never any theorem left as `sorry`.

The mathematics, Lean proof, and literature searches were produced by AI agents. No human has reviewed this project.

## References and attribution

* A. Schinzel, [*Sur un problème de P. Erdős*](https://doi.org/10.4064/cm-5-2-198-204), Colloq. Math. 5 (1958) 198-204, with a letter of Erdős (5 February 1957); *P 217, R 1*, Colloq. Math. 10 (1963) 365.
* [Erdős Problems #387](https://www.erdosproblems.com/387) and [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/387.lean#L62)
* H. M. Bui, S. Naprienko, K. Pratt, and A. Zaharescu, [arXiv:2605.21221](https://arxiv.org/abs/2605.21221), answered the headline problem and construct covers for many $k$, though not all large ones. P. Erdős, [Rocky Mountain J. Math. 15 (1985)](https://users.renyi.hu/~p_erdos/1985-27.pdf), pp. 358-359, has the remark on Lacampagne and Selfridge.
* The reduction to a cover, default class zero, auxiliary prime, and large primes at the end are due to Schinzel and Erdős. Full credits are in [Erdos387.lean](Erdos387.lean) and [Erdos387.md](Erdos387.md#what-is-new-and-what-is-borrowed).
* [Prior-art audit](../PRIOR_ART.md#erdős-387-schinzels-conjecture-for-large-k)
