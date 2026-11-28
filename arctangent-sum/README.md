# Arctangent-sum conjecture (`arXiv:2607.05739`)

Start adding the angles $\arctan 1, \arctan 2, \arctan 3, \ldots$ and take the tangent of the running total:

$$
x_n = \tan\!\left(\sum_{k=1}^n \arctan k\right).
$$

Remarkably, the first four terms are all integers: $x_1 = 1$, $x_2 = -3$, $x_3 = 0$, and $x_4 = 4$ (and then $x_5 = -9/19$). Amdeberhan, Medina, and Moll conjectured that $x_n$ is **never** an integer for any $n \ge 5$. That conjecture remains open, though Ken Ono (`arXiv:2607.05739`) proved that integer values are at least logarithmically rare: at most $O(\log N)$ positive indices $n \le N$ produce an integer.

The Lean 4 proofs here strengthen the known partial results on several fronts: they sharpen the sparsity bound to $O((\log N)^{3/4})$, rule out all counterexamples in the range $5 \le n \le 10^6$, show that any counterexample must be huge ($\lvert x_n \rvert > n^{10} > 10^{60}$, with an exponential lower bound for $n \ge 2^{27}$), and eliminate infinite residue classes modulo inert primes.

| Field | Summary |
| --- | --- |
| Problem | Arctangent-sum conjecture (Amdeberhan, Medina, and Moll), Ken Ono (`arXiv:2607.05739`), `FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean` |
| Status | Partial results (sparsity and lower bounds). Ruling out all $n \ge 5$ remains open. |
| Main theorems | `Arxiv.«2607.05739».positive_integer_count_isBigO`, `counterexample_constraints`, `bounded_integer_iff`, `tan_int_exponential`, `not_isIntegerValue_of_residue` in [ArctanSum.lean](ArctanSum.lean) |
| Verification | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib v4.36.0) |
| Prior art | Checked 23 November 2026: Ken Ono proved $O(\log N)$, and Formal Conjectures links the earlier Lean formalization of Ono's results while listing the full conjecture as open. See [PRIOR_ART.md](../PRIOR_ART.md#arctangent-sum-conjecture). |

## How the mathematics works

**Turning trigonometry into Gaussian integers:** Because $\arctan k$ is the angle of the complex number $1 + ik$, adding angles corresponds to multiplying **Gaussian integers** (complex numbers $a + bi$ with $a, b \in \mathbb{Z}$). Setting

$$
A_n + i B_n = \prod_{k=1}^n (1 + ik),
$$

we obtain $x_n = B_n / A_n$ without any trigonometric functions or rational division! For example:

* $n = 1$: $1 + i \implies x_1 = 1/1 = 1$
* $n = 2$: $(1 + i)(1 + 2i) = -1 + 3i \implies x_2 = -3$
* $n = 3$: $(-1 + 3i)(1 + 3i) = -10 + 0i \implies x_3 = 0$
* $n = 4$: $(-10)(1 + 4i) = -10 - 40i \implies x_4 = 4$
* $n = 5$: $(-10 - 40i)(1 + 5i) = 190 - 90i \implies x_5 = -9/19$

Thus $x_n = m \in \mathbb{Z}$ if and only if $A_n \mid B_n$, and taking squared norms yields $\prod_{k=1}^n (1 + k^2) = A_n^2 (1 + m^2)$. This ties integer values of $x_n$ directly to the prime factorization of $\prod_{k=1}^n (1 + k^2)$, which drives the magnitude bounds ($|m| > n^{10}$ and the exponential bound) and the sharpened $O((\log N)^{3/4})$ sparsity bound.

**Why inert primes knock out whole arithmetic progressions:** A prime $p \equiv 3 \pmod 4$ is called **inert** in $\mathbb{Z}[i]$ because it remains prime (does not factor) in the Gaussian integers, so $p$ can never divide $1 + k^2$. Consequently, $p$ never divides $A_n$ and $B_n$ simultaneously, and multiplying by a full block of $p$ consecutive factors scales $(A_n, B_n) \bmod p$ by a nonzero real residue. Whenever $A_r \equiv 0 \pmod p$ for some remainder $r$ (for example, $A_5 = 190 = 10 \cdot 19 \equiv 0 \pmod{19}$), $p$ divides $A_n$ without dividing $B_n$ for *every* $n \equiv r \pmod p$, ruling out the entire infinite residue class at once.

## Main Lean results

All declarations below are in namespace `Arxiv.«2607.05739»` in [ArctanSum.lean](ArctanSum.lean):

| Declaration | Result |
| --- | --- |
| `positive_integer_count_isBigO` | The number of positive indices $n \le N$ with $x_n \in \mathbb{Z}$ is $O((\log N)^{3/4})$, improving Ono's $O(\log N)$ bound ([ArctanSparsity.lean](ArctanSparsity.lean)). |
| `counterexample_constraints` | If $n \ge 5$ and $x_n \in \mathbb{Z}$, then $n > 10^6$, $\lvert x_n \rvert > n^{10}$, and $\lvert x_n \rvert > 10^{60}$. |
| `bounded_integer_iff` | For $n > 0$, $x_n$ is an integer with $\lvert x_n \rvert \le 10^6$ if and only if $n \le 4$ (giving $1, -3, 0, 4$ via `known_values`). |
| `tan_int_exponential` | For $n \ge 2^{27}$ with integer $x_n = m$, $2^{\lfloor n/4 \rfloor} \le 1 + m^2$. |
| `not_isIntegerValue_of_residue`, `not_isIntegerValue_mod19`, `not_isIntegerValue_mod331` | Infinite residue-class exclusions modulo inert primes $p \equiv 3 \pmod 4$, including $n \equiv 5, 13 \pmod{19}$ and $n \equiv 7, 77, 253, 323 \pmod{331}$. |

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
