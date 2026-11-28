# Erdős Problem #211: refuting the constant 1/6

Take $n$ points in the plane and draw every line that passes through at least two of them. Provided the points are not almost all piled onto one line — specifically, at most $n - k$ lie on any single line — a 1983 theorem of Beck, and independently Szemerédi and Trotter, guarantees at least $ckn$ distinct lines for some absolute constant $c > 0$.

In 1984, Erdős wondered whether $c = 1/6$ works and suggested looking for a counterexample first. Our Lean 4 proof supplies one: there are arbitrarily large sets of $n$ points, with at most $O(n^{2/3})$ points on any line, that determine at most $0.166\,n^2$ lines (strictly below $kn/6 \approx 0.16667\,n^2$). Beck's theorem itself is unaffected.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #211, $1/6$ variant (`erdosproblems.com/211`), `erdos_211.variants.one_sixth` in `FormalConjectures/ErdosProblems/211.lean` |
| Status | Variant refuted, even in the weak form with a $(1 - \varepsilon)$ factor and for large $n$. The counterexample needs $k$ close to $n$ (above about $0.996\,n$); nothing is proved for smaller $k$. |
| Main theorems | `main : ¬ type_of% @Erdos211.erdos_211.variants.one_sixth` in [Erdos211.lean](Erdos211.lean); quantitative form `E211.counterexample` |
| Verification | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos211` (Lean 4.33.1 + Formal Conjectures) |
| Prior art | Checked 25 November 2026: two limited searches found no earlier disproof of the constant $1/6$. The line count itself is not claimed as new mathematics. |

## What Lean proves

| Lean declaration | Result |
| --- | --- |
| `main` | It is false that for every $\varepsilon > 0$ and all large $n$, every such point set determines at least $(1-\varepsilon)kn/6$ lines uniformly in $1 \le k < n$. |
| `E211.counterexample` (internal) | For $R = 30030M$ with $M \ge 1000$: a set of $n \ge 3R^3$ points with at most $2R^2$ on any line that determines at most $0.166\,kn$ lines, where $k = n - 2R^2$. |

## Idea of the proof

The counterexample is a projective grid of rational points — obtained by projecting a 3D integer box from the origin onto the plane $z = 1$:

1. **The point set.** Take all integer vectors $(x, y, z)$ with $-R \le x, y < R$ and $1 \le z < R$, and project them to the planar points $(x/z, y/z)$. Distinct *primitive* vectors (those whose coordinates share no common prime factor) yield distinct points, giving about $4R^3/\zeta(3) \approx 3.33\,R^3$ points in all, with at most $2R^2 = O(n^{2/3})$ on any single line.
2. **Charging each line to a minimal-height spanning pair.** A line determined by these points corresponds to a 2D plane through the origin in $\mathbb{R}^3$. Charge each line to a pair of integer vectors $(u, w)$ spanning it whose sum of heights $z(u) + z(w)$ is as small as possible.
3. **Two strong filters on minimal pairs.** Apart from the negligible $O(R^5)$ pairs with $z(u) = z(w)$, any height-minimal pair with $z(u) > z(w)$ must pass two tests:
   * *Far apart in $x$ or $y$:* $u - w$ cannot stay inside the box (otherwise $u - w$ would replace $u$ with smaller height), so $u$ and $w$ must differ by at least $R$ in $x$ or in $y$ — eliminating roughly $9/16$ of all pairs.
   * *Linearly independent modulo every prime:* otherwise some integer combination $(au + bw)/p$ would lie inside the box with smaller height and replace one of the vectors.
4. **Counting modulo $30030$.** Splitting coordinates into coarse quotients and fine residues modulo $30030 = 2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13$ enforces both filters simultaneously (using only the first six primes) and already forces the line count below $0.166\,kn < kn/6$.

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos211
```

`lake build` checks the proof, confirms that `main` matches the upstream statement type (via `type_of%`), and verifies that `main` uses only `propext`, `Classical.choice`, and `Quot.sound`. `leanchecker` replays the module in the Lean kernel. The first build also compiles the imported part of Formal Conjectures (pinned at commit `9097e2f9`). We use only its statements, definitions, and proved lemmas, never any theorem left as `sorry`.

The mathematics, Lean proof, and literature searches were produced by AI agents. No human has reviewed this project.

## References and attribution

* P. Erdős, [*Research problems*](https://users.renyi.hu/~p_erdos/1984-18.pdf), Period. Math. Hungar. 15 (1984) 101-103.
* [Erdős Problems #211](https://www.erdosproblems.com/211) and [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/211.lean#L67)
* J. Beck, Combinatorica 3 (1983) 281-297; E. Szemerédi and W. T. Trotter, Combinatorica 3 (1983) 381-392; F. de Zeeuw, [arXiv:1802.08015](https://arxiv.org/abs/1802.08015) (lower bound constant $1/9$).
* The ingredients are classical. For a close variant of our point set, the line count follows from W. M. Schmidt's count of primitive sublattices (1998); we found no source drawing this conclusion. Full credits are in [Erdos211.lean](Erdos211.lean).
