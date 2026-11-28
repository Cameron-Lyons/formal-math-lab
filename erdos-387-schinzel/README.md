# Erdős Problem #387: Schinzel's conjecture for all large $k$

Look at the binomial coefficient $\binom{n}{k} = \frac{n(n-1)\cdots(n-k+1)}{k!}$. For a fixed integer $k$, can we find an integer $n$ such that **none** of the $k$ consecutive factors $n, n-1, \dots, n-k+1$ divides $\binom{n}{k}$?

When $k$ is a prime power, Schinzel (1958) proved the answer is **no**: one of those $k$ factors must always divide $\binom{n}{k}$. In *Colloq. Math.* Problem P 217, he asked whether this failure can happen for infinitely many non-prime-powers $k$, expecting the answer to be no. This project gives a machine-checked Lean 4 proof of Schinzel's conjecture for all sufficiently large $k$: if $k$ is large enough and not a prime power, such an $n$ always exists. Because the lower bound on $k$ is not explicit, nothing is proved for any specific $k$. (The headline question of Erdős Problem #387 is a separate problem answered elsewhere.)

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #387, Schinzel variant (`erdosproblems.com/387`), Colloq. Math. P 217, `erdos_387.variants.schinzel` in `FormalConjectures/ErdosProblems/387.lean` |
| Status | Eventual form proved. The explicit form (every non-prime-power $k \ge 35$) remains open. |
| Main theorem | `main : type_of% @Erdos387.erdos_387.variants.schinzel` in [Erdos387.lean](Erdos387.lean) |
| Written proof | [Erdos387.md](Erdos387.md), with the same lemma numbers as the Lean file |
| Verification | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos387` (Lean 4.33.1 + Formal Conjectures) |
| Prior art | Checked 25 November 2026: no earlier proof of the all-large-$k$ statement was found. Erdős wrote in 1985 that Lacampagne and Selfridge could probably prove it, though no paper was found. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-387-schinzels-conjecture-for-large-k). |

## How the proof works

1. **Reduction to a covering problem (Schinzel).** By Kummer's theorem (the exponent of a prime $p$ in $\binom{n}{k}$ counts carries when adding $k$ and $n-k$ in base $p$) and the Chinese remainder theorem, it suffices to choose for each prime $p \le k$ an admissible residue class $a_p$ satisfying $k \bmod p < a_p \le p$ so that these classes cover every integer in $\{1, \dots, k\}$.
2. **Default setup and two special primes.** Start by putting every prime $p \le k$ into class $0$ ($a_p = p$), which covers $2, \dots, k$ and leaves only $1$ uncovered. Move the largest prime factor $q$ of $k$ to class $1$ (covering $1$, while a second prime factor $q'$ of $k$—which exists because $k$ is not a prime power—stays in class $0$ to keep $k$ covered). Also move one auxiliary prime $p_0$, found via Turán's second moment, to a class $c_0$ containing at least $k/(\log k)^{14}$ large primes near $k$.
3. **Greedy level-by-level covering with parity lifting.** Any remaining uncovered number must be composed entirely of moved primes. We process uncovered numbers in order of their **level** $\min(n, k-n)$ up to $k/5$, giving each a fresh odd prime $p$ that divides an even number $k - i$ ($i < l$). A parity argument shows that every newly uncovered multiple of $p$ lands at a strictly higher level ($\ge p$), preventing any backward cascade.
4. **Controlling supply vs. demand, and cleanup.** Chebyshev's bounds and Størmer's theorem guarantee a steady supply of fresh primes, while Rankin's method, a short-window prime assignment, and a carefully tuned decreasing weight function prove that the number of uncovered smooth integers never catches up. At the end, only at most $k/(\log k)^{14}$ uncovered numbers remain—all at level $\ge k/5$—and we cover them with distinct large primes $P \equiv c_0 \pmod{p_0}$; moving such a $P$ uncovers only $P$ itself, which $p_0$ already covers.

The Lean proof is about 2,400 lines long. For a complete, self-contained written proof with roadmap, motivation, and appendix proofs of Størmer's theorem and Chebyshev's bounds, see [Erdos387.md](Erdos387.md).

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos387
```

**Trust boundary and verification notes:**

* `lake build` checks the proof, confirms that `main` matches the upstream statement type (via `type_of%`), and verifies that `main` uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
* `leanchecker` replays the compiled module independently in the Lean kernel.
* The first build also compiles the imported part of Formal Conjectures (pinned at commit `9097e2f9`). We use only its statements, definitions, and proved lemmas, never any theorem left as `sorry`.
* The mathematics, Lean proof, and literature searches were produced by AI agents. No human has reviewed this project.

## References and attribution

* A. Schinzel, [*Sur un problème de P. Erdős*](https://doi.org/10.4064/cm-5-2-198-204), Colloq. Math. 5 (1958) 198-204, with a letter of Erdős (5 February 1957); *P 217, R 1*, Colloq. Math. 10 (1963) 365.
* [Erdős Problems #387](https://www.erdosproblems.com/387) and [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/387.lean#L62)
* H. M. Bui, S. Naprienko, K. Pratt, and A. Zaharescu, [arXiv:2605.21221](https://arxiv.org/abs/2605.21221), answered the headline problem and construct covers for many $k$, though not all large ones. P. Erdős, [Rocky Mountain J. Math. 15 (1985)](https://users.renyi.hu/~p_erdos/1985-27.pdf), pp. 358-359, has the remark on Lacampagne and Selfridge.
* The reduction to a cover, default class zero, auxiliary prime, and large primes at the end are due to Schinzel and Erdős. Full credits are in [Erdos387.lean](Erdos387.lean) and [Erdos387.md](Erdos387.md#what-is-new-and-what-is-borrowed).
* [Prior-art audit](../PRIOR_ART.md#erdős-387-schinzels-conjecture-for-large-k)
