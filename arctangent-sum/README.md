# Arctangent-sum conjecture (arXiv:2607.05739): O((log N)^(3/4)) sparsity and n > 10^6 bound — Lean 4 proofs

**Status: the full conjecture remains open.** Define

$$
x_n = \tan\!\left(\sum_{k=1}^n \arctan k\right).
$$

The first four values are $x_1 = 1$, $x_2 = -3$, $x_3 = 0$, and $x_4 = 4$. Amdeberhan, Medina, and Moll conjectured that $x_n$ is never an integer for any $n \ge 5$. Ken Ono (`arXiv:2607.05739`) proved that at most $O(\log N)$ positive indices $n \le N$ give integer values.

This Lean 4 project sharpens the sparsity bound to **$O((\log N)^{3/4})$**, verifies that no counterexample exists for **$5 \le n \le 10^6$** (and any counterexample must satisfy **$|x_n| > n^{10} > 10^{60}$**, plus an exponential bound for $n \ge 2^{27}$), and proves infinite residue-class exclusions modulo inert primes.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Arctangent-sum conjecture**, `tan(sum_{k=1}^n arctan k)` integer values, Amdeberhan–Medina–Moll conjecture, Ken Ono (`arXiv:2607.05739`), `FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean` |
| **Status** | **Partial results (sharpened sparsity and lower bounds).** Excluding all $n \ge 5$ remains open. |
| **Main Lean theorems** | `Arxiv.«2607.05739».positive_integer_count_isBigO`, `counterexample_constraints`, `bounded_integer_iff`, `tan_int_exponential`, `not_isIntegerValue_of_residue` in [ArctanSum.lean](ArctanSum.lean) |
| **Verification** | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib v4.36.0) |
| **Prior-art status** | Checked **23 November 2026**: Ken Ono proved $O(\log N)$ and Formal Conjectures links the earlier Lean formalization of Ono's results while listing the full conjecture as open. See [PRIOR_ART.md](../PRIOR_ART.md#arctangent-sum-conjecture). |

## Main Lean results

All declarations below are in namespace `Arxiv.«2607.05739»` in [ArctanSum.lean](ArctanSum.lean):

| Declaration | Result |
| --- | --- |
| `positive_integer_count_isBigO` | The number of positive indices $n \le N$ with $x_n \in \mathbb{Z}$ is $O((\log N)^{3/4})$, sharpening Ono's $O(\log N)$ bound. [Proof outline](ArctanSparsity.lean) |
| `counterexample_constraints` | If $n \ge 5$ and $x_n \in \mathbb{Z}$, then $n > 10^6$, $|x_n| > n^{10}$, and $|x_n| > 10^{60}$. |
| `bounded_integer_iff` | For $n > 0$, $x_n$ is an integer with $|x_n| \le 10^6$ if and only if $n \le 4$ (attaining $1, -3, 0, 4$ via `known_values`). |
| `tan_int_exponential` | For $n \ge 2^{27}$ with integer $x_n = m$, $2^{\lfloor n/4 \rfloor} \le 1 + m^2$. |
| `not_isIntegerValue_of_residue`, `not_isIntegerValue_mod19`, `not_isIntegerValue_mod331` | Unbounded residue-class exclusions modulo primes $p \equiv 3 \pmod 4$ (including $n \equiv 5, 13 \pmod{19}$ and $n \equiv 7, 77, 253, 323 \pmod{331}$). |

## Build

From this directory with Lean and mathlib pinned to **v4.36.0**:

```sh
lake exe cache get
lake build
```

## References and attribution

* [Ken Ono, `arXiv:2607.05739`](https://arxiv.org/abs/2607.05739)
* [Formal Conjectures `TanArctanSum.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean) · [Formal Conjectures docs](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/Arxiv/%C2%AB2607.05739%C2%BB/TanArctanSum/)
* Four definitions in the Gaussian-integer model in [ArctanBridge.lean](ArctanBridge.lean) come from Formal Conjectures (copyright 2026 The Formal Conjectures Authors, [Apache-2.0 license](https://github.com/google-deepmind/formal-conjectures/blob/main/LICENSE)).
* [Dated prior-art audit](../PRIOR_ART.md#arctangent-sum-conjecture)
