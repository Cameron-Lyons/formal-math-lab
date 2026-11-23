# The arctangent-sum conjecture

Let $x_n=\tan(\sum_{k=1}^n\arctan k)$. The first four values are $1,-3,0,4$.
Amdeberhan, Medina and Moll conjectured that these are the only positive indices
with an integer value. The conjecture remains open. [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean)

## Lean results

- `counterexample_constraints` proves that if $n\ge5$ and $x_n$ is an integer, then $n>10^6$ and $|x_n|>n^{10}>10^{60}$. [Theorem](ArctanSum.lean#L32)
- `positive_integer_count_isBigO` proves that the number of positive indices $n\le N$ with integer $x_n$ is $O((\log N)^{3/4})$, sharpening Ono's $O(\log N)$ bound. [Theorem](ArctanSum.lean#L47) · [Proof outline](ArctanSparsity.lean) · [Ono's paper](https://arxiv.org/abs/2607.05739)

## Build

From this directory, run `lake build`. The project pins Lean and Mathlib to
4.36.0. On a fresh checkout, `lake exe cache get` downloads Mathlib's build cache.

Four definitions in the Gaussian-integer model come from Formal Conjectures,
copyright 2026 The Formal Conjectures Authors, under Apache 2.0. [Source notice](ArctanBridge.lean) · [License](https://github.com/google-deepmind/formal-conjectures/blob/main/LICENSE)
