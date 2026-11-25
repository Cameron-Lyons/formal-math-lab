# Erdős Problem #211: refuting the constant 1/6

Beck, and Szemerédi and Trotter, proved in 1983 that $n$ points in the plane with at most $n - k$ on any line determine at least $ckn$ lines for an absolute constant $c > 0$. Erdős (1984) wondered whether $c = 1/6$ works and suggested looking for a counterexample first. The Lean 4 proof here gives one: there are arbitrarily large sets of $n$ points, with at most $O(n^{2/3})$ on any line, that determine at most $0.166\,n^2$ lines. Beck's theorem is unaffected.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #211, $1/6$ variant (`erdosproblems.com/211`), `erdos_211.variants.one_sixth` in `FormalConjectures/ErdosProblems/211.lean` |
| Status | Variant refuted, in the weak form with a factor $1 - \varepsilon$ and for large $n$. The counterexample needs $k$ close to $n$ (above about $0.996\,n$); nothing is proved for smaller $k$. |
| Main theorems | `main : ¬ type_of% @Erdos211.erdos_211.variants.one_sixth` in [Erdos211.lean](Erdos211.lean); quantitative form `E211.counterexample` |
| Written proof | [Erdos211.md](Erdos211.md), with the same lemma numbers as the Lean file |
| Verification | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos211` (Lean 4.33.1 + Formal Conjectures) |
| Prior art | Checked 25 November 2026: no earlier disproof of the constant $1/6$ located in two limited searches. The line count itself is not claimed as new mathematics. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-211-the-constant-one-sixth). |

## What Lean proves

| Lean declaration | Result |
| --- | --- |
| `main` | It is false that for every $\varepsilon > 0$ and all large $n$, every such set determines at least $(1-\varepsilon)kn/6$ lines uniformly in $1 \le k < n$. |
| `E211.counterexample` (internal) | For $R = 30030M$, $M \ge 1000$: a set of $n \ge 3R^3$ points with at most $2R^2$ on any line that determines at most $0.166\,kn$ lines, where $k = n - 2R^2$. |

## Idea of the proof

Take the points $(x/z, y/z)$ with $-R \le x, y < R$ and $1 \le z < R$. Charge every determined line to the spanning pair of integer vectors with the smallest sum of heights $z$. Such a pair differs by at least $R$ in $x$ or in $y$, and it is independent modulo every prime. Counting pairs with these properties modulo $30030 = 2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13$ gives fewer than $n^2/6$ lines.

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos211
```

`lake build` checks the proof, verifies that the type of `main` matches the upstream statement (`type_of%`), and confirms that `main` uses only `propext`, `Classical.choice`, and `Quot.sound`. `leanchecker` replays the module in the Lean kernel. The first build also compiles the part of Formal Conjectures imported by the statement. Formal Conjectures is pinned at commit `9097e2f9`; only its statements, definitions, and proved lemmas are used, never the theorem it leaves as `sorry`.

The mathematics, Lean proof, and literature searches are the work of AI agents. No human has reviewed this project.

## References and attribution

* P. Erdős, [*Research problems*](https://users.renyi.hu/~p_erdos/1984-18.pdf), Period. Math. Hungar. 15 (1984) 101-103.
* [Erdős Problems #211](https://www.erdosproblems.com/211) and [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/211.lean#L67)
* J. Beck, Combinatorica 3 (1983) 281-297; E. Szemerédi and W. T. Trotter, Combinatorica 3 (1983) 381-392; F. de Zeeuw, [arXiv:1802.08015](https://arxiv.org/abs/1802.08015) (lower constant $1/9$).
* The ingredients are classical. For a close relative of the point set, the number of lines follows from W. M. Schmidt's count of primitive sublattices (1998); no one was found who drew this conclusion. Full credits are in [Erdos211.lean](Erdos211.lean) and [Erdos211.md](Erdos211.md#what-is-new-and-what-is-borrowed).
* [Prior-art audit](../PRIOR_ART.md#erdős-211-the-constant-one-sixth)
