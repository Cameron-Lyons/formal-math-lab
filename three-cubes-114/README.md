# Sum of three cubes: $x^3 + y^3 + z^3 = 114$

Can 114 be written as a sum of three integer cubes (positive, negative, or zero),

$$
x^3 + y^3 + z^3 = 114?
$$

Because every cube is $0$ or $\pm 1 \pmod 9$, numbers congruent to $4$ or $5 \pmod 9$ are impossible—but $114 \equiv 6 \pmod 9$ faces no such obstruction. Still, no integer solution is known, and existence remains open.

Every modern search for $x^3 + y^3 + z^3 = 114$ starts from one factorization:

$$
x^3 + y^3 = (x + y)(x^2 - xy + y^2) = 114 - z^3 \implies (x + y) \mid (z^3 - 114).
$$

Setting the pair sum $a = x + y$ and modulus $M = |x + y|$, any solution makes $z$ a **cube root of 114 modulo $M$** ($z^3 \equiv 114 \pmod M$). Once $a$ and $z$ are chosen, $x$ and $y$ are recovered from a quadratic equation whose discriminant must be a perfect square.

The Lean 4 proofs here establish a sharp limitation of the **full $\mathbb{Z}[\sqrt[3]{114}]$ norm method** for selecting candidate moduli $M$: arbitrarily large moduli $M$ admit a cube root of 114 yet never appear as a norm from $\mathbb{Z}[\sqrt[3]{114}]$. Lean also kernel-verifies modular sieve filters modulo $5, 18, 19, 25, 27, 32,$ and $19^2$, proves exactness of the square-root recovery step, and certifies the discriminants from a bounded Python search.

| Field | Summary |
| --- | --- |
| Problem | Sum of three cubes $x^3 + y^3 + z^3 = 114$, Booker and Sutherland (`arXiv:2007.01209`), Grantham and Walsh (`arXiv:2211.12149`), Welsh (`arXiv:2008.00538`) |
| Status | Partial results (norm-method obstruction, Lean-verified sieve filters, and finite negative searches). Existence of an integer solution remains open. |
| Main theorems | `ThreeCubes114.TernaryNorm.unbounded_normalized_moduli`, `family_cube_root`, `family_noncubes` ([TernaryFamily.lean](TernaryFamily.lean)); `ThreeCubes114.ramified19_of_solution`, `even_pair_sieve`, `progression_congruences`, `recoverPair_complete` ([ThreeCubes114.lean](ThreeCubes114.lean)) |
| Verification | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib v4.36.0); `uv run TernaryOtherRoots.py --full` for the finite pair-sum search |
| Prior art | Checked 23 November 2026: Booker-Sutherland and Grantham-Walsh give earlier search methods and Welsh gives the cubic-ideal correspondence; priority of the elementary mod-19 norm obstruction is unverified. See [PRIOR_ART.md](../PRIOR_ART.md#three-integer-cubes-summing-to-114). |

## Main results

### 1. Why the full $\mathbb{Z}[\sqrt[3]{114}]$ norm family misses infinitely many candidate moduli

One algebraic way to generate candidate moduli $M$ with a cube root of 114 is to take absolute norms of elements $u + v\sqrt[3]{114} + w(\sqrt[3]{114})^2 \in \mathbb{Z}[\sqrt[3]{114}]$. A short mod-19 calculation shows this misses an entire infinite family of valid moduli:

- For any integer $n \ge 1$, set $M = 361n^3 + 6 = 19^2 n^3 + 6$ and $r = -19n$.
- Since $19 \cdot 6 = 114$, we have
  $$
  r^3 - 114 = -19^3 n^3 - 19 \cdot 6 = -19(19^2 n^3 + 6) = -19M,
  $$
  so $r^3 \equiv 114 \pmod M$: every modulus $M$ in this sequence admits a cube root of 114 (`family_cube_root`).
- Meanwhile, because $19 \mid 114$, the norm of $u + v\sqrt[3]{114} + w(\sqrt[3]{114})^2$ collapses modulo 19 to $u^3 \pmod{19}$. Every absolute norm from $\mathbb{Z}[\sqrt[3]{114}]$ must therefore be a cube modulo 19—namely one of $0, \pm 1, \pm 7, \pm 8 \pmod{19}$.
- Yet $M = 19^2 n^3 + 6 \equiv 6 \pmod{19}$ (and $-M \equiv -6 \pmod{19}$), neither of which is a cube modulo 19 (`family_noncubes`).

Hence arbitrarily large candidate moduli $M$ having a cube root of 114 lie completely outside the full norm family (`ThreeCubes114.TernaryNorm.unbounded_normalized_moduli` in [TernaryFamily.lean](TernaryFamily.lean); norm formula in [TernaryNorm.lean](TernaryNorm.lean)).

### 2. Kernel-checked modular sieves and exact pair recovery

In [ThreeCubes114.lean](ThreeCubes114.lean), Lean's kernel verifies the modular filters used when searching by pair sum $a = x + y$:

- `progression_congruences`: $(x + y) \equiv 1 \pmod 3$ and $x + y + z \equiv 0 \pmod{18}$.
- `ramified19_of_solution`: whenever $19 \mid (x + y)$, the quotient $(x + y)/19 \bmod 19$ must lie in 9 of the 19 residue classes (`[2, 3, 8, 10, 12, 13, 14, 15, 18]`); `ramified19_local_witness` proves this characterizes the mod-$19^2$ obstruction exactly.
- `even_pair_sieve`: an even pair sum allows only 8 combinations of $(x + y \bmod 32,\ z \bmod 8)$.
- `five_step_filter` and `five_example`: arithmetic-progression step filters when $5 \mid (x + y)$.
- `recoverPair_complete`: proves that the exact integer square-root check on the quadratic discriminant recovers every integer solution $(x, y, z)$.

## Reproduce

### 1. Lean kernel proofs

Run from this directory with Lean and mathlib pinned to v4.36.0:

```sh
lake exe cache get
lake build
```

### 2. Bounded negative search and discriminant certificates

To reproduce the external Python search over 2,504,020 selected pair sums in the band $3M \le |z| < 51M$ (script: [TernaryOtherRoots.py](TernaryOtherRoots.py)):

```sh
uv run TernaryOtherRoots.py --full
```

Only 8 candidate discriminants survive all modular filters; [NormCertificates.lean](NormCertificates.lean) checks in Lean's kernel that each of those 8 discriminants lies strictly between two consecutive perfect squares (and hence yields no integer solution).

## References

- [Booker and Sutherland, `arXiv:2007.01209`, §5.2](https://arxiv.org/pdf/2007.01209#page=14)
- [Grantham and Walsh, `arXiv:2211.12149`](https://arxiv.org/abs/2211.12149)
- [Welsh, `arXiv:2008.00538`, Theorem 3](https://arxiv.org/abs/2008.00538)
- [Prior-art audit](../PRIOR_ART.md#three-integer-cubes-summing-to-114)
