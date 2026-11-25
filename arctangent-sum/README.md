# Arctangent-sum conjecture (`arXiv:2607.05739`)

Define

$$
x_n = \tan\!\left(\sum_{k=1}^n \arctan k\right).
$$

The first four values are $x_1 = 1$, $x_2 = -3$, $x_3 = 0$, and $x_4 = 4$. Amdeberhan, Medina, and Moll conjectured that $x_n$ is never an integer for $n \ge 5$; that full conjecture remains open. Ken Ono (`arXiv:2607.05739`) proved that at most $O(\log N)$ positive indices $n \le N$ give integer values.

The Lean 4 proofs here tighten the sparsity bound to $O((\log N)^{3/4})$, rule out counterexamples for $5 \le n \le 10^6$ (showing any counterexample satisfies $|x_n| > n^{10} > 10^{60}$, with an exponential bound for $n \ge 2^{27}$), and establish infinite residue-class exclusions modulo inert primes.

| Field | Summary |
| --- | --- |
| Problem | Arctangent-sum conjecture (Amdeberhan, Medina, and Moll), Ken Ono (`arXiv:2607.05739`), `FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean` |
| Status | Partial results (sparsity and lower bounds). Excluding all $n \ge 5$ remains open. |
| Main theorems | `Arxiv.«2607.05739».positive_integer_count_isBigO`, `counterexample_constraints`, `bounded_integer_iff`, `tan_int_exponential`, `not_isIntegerValue_of_residue` in [ArctanSum.lean](ArctanSum.lean) |
| Verification | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib v4.36.0) |
| Prior art | Checked 23 November 2026: Ken Ono proved $O(\log N)$ and Formal Conjectures links the earlier Lean formalization of Ono's results while listing the full conjecture as open. See [PRIOR_ART.md](../PRIOR_ART.md#arctangent-sum-conjecture). |

## Main Lean results

All declarations below are in namespace `Arxiv.«2607.05739»` in [ArctanSum.lean](ArctanSum.lean):

| Declaration | Result |
| --- | --- |
| `positive_integer_count_isBigO` | The number of positive indices $n \le N$ with $x_n \in \mathbb{Z}$ is $O((\log N)^{3/4})$, improving Ono's $O(\log N)$ bound ([ArctanSparsity.lean](ArctanSparsity.lean)). |
| `counterexample_constraints` | If $n \ge 5$ and $x_n \in \mathbb{Z}$, then $n > 10^6$, $|x_n| > n^{10}$, and $|x_n| > 10^{60}$. |
| `bounded_integer_iff` | For $n > 0$, $x_n$ is an integer with $|x_n| \le 10^6$ if and only if $n \le 4$ (attaining $1, -3, 0, 4$ via `known_values`). |
| `tan_int_exponential` | For $n \ge 2^{27}$ with integer $x_n = m$, $2^{\lfloor n/4 \rfloor} \le 1 + m^2$. |
| `not_isIntegerValue_of_residue`, `not_isIntegerValue_mod19`, `not_isIntegerValue_mod331` | Unbounded residue-class exclusions modulo primes $p \equiv 3 \pmod 4$ (including $n \equiv 5, 13 \pmod{19}$ and $n \equiv 7, 77, 253, 323 \pmod{331}$). |

## Build

From this directory with Lean and mathlib pinned to v4.36.0:

```sh
lake exe cache get
lake build
```

## References and attribution

* [Ken Ono, `arXiv:2607.05739`](https://arxiv.org/abs/2607.05739)
* [Formal Conjectures `TanArctanSum.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean) and [docs](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/Arxiv/%C2%AB2607.05739%C2%BB/TanArctanSum/)
* Four definitions in the Gaussian-integer model in [ArctanBridge.lean](ArctanBridge.lean) come from Formal Conjectures (copyright 2026 The Formal Conjectures Authors, [Apache-2.0 license](https://github.com/google-deepmind/formal-conjectures/blob/main/LICENSE)).
* [Prior-art audit](../PRIOR_ART.md#arctangent-sum-conjecture)
