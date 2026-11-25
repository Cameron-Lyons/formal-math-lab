# Sum of three cubes x^3 + y^3 + z^3 = 114: norm obstructions, modular sieves, and bounded searches — Lean 4 proofs

**Status: no integer solution to $x^3 + y^3 + z^3 = 114$ is known, and existence remains open.** For any integer solution, the pair sum $M = |x + y|$ must divide $z^3 - 114$.

This Lean 4 project proves a **structural limitation of the full $\mathbb{Z}[\sqrt[3]{114}]$ norm method** for selecting candidate moduli $M$ (arbitrarily large $M$ admit a cube root of 114 yet lie outside the norm family), proves exact **modular sieve filters** modulo 5, 18, 19, 25, 27, 32, and $19^2$, and records bounded searches and exact discriminant certificates (which found no integer solution).

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Sum of three cubes** `x^3 + y^3 + z^3 = 114` (smallest remaining open case below 1000 alongside 390, 579, ...), Booker–Sutherland (`arXiv:2007.01209`), Grantham–Walsh (`arXiv:2211.12149`), Welsh (`arXiv:2008.00538`) |
| **Status** | **Partial results (norm-method obstruction, Lean-verified sieve filters, and finite negative searches).** Existence of an integer solution to $x^3 + y^3 + z^3 = 114$ remains open. |
| **Main Lean theorems** | `ThreeCubes114.TernaryNorm.unbounded_normalized_moduli`, `family_cube_root`, `family_noncubes` ([TernaryFamily.lean](TernaryFamily.lean)); `ThreeCubes114.ramified19_of_solution`, `even_pair_sieve`, `progression_congruences`, `recoverPair_complete` ([ThreeCubes114.lean](ThreeCubes114.lean)) |
| **Verification** | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib v4.36.0); `uv run TernaryOtherRoots.py --full` for the finite pair-sum search |
| **Prior-art status** | Checked **23 November 2026**: Booker–Sutherland and Grantham–Walsh give earlier search methods and Welsh gives the cubic-ideal correspondence; historical priority of the elementary mod-19 norm obstruction is unverified. See [PRIOR_ART.md](../PRIOR_ART.md#three-integer-cubes-summing-to-114). |

## Main results

### Limitation of the full norm family

Take any integer $n \ge 1$, set $M = 361n^3 + 6 = 19^2 n^3 + 6$, and put $r = -19n$. Then $r^3 - 114 = -19M$, so $114$ has a cube root modulo $M$. However, every absolute norm from $\mathbb{Z}[\sqrt[3]{114}]$ is a cube modulo $19$ (namely $0, \pm 1, \pm 7, \pm 8 \pmod{19}$), whereas $M \equiv 6 \pmod{19}$. Thus arbitrarily large moduli $M$ admitting a cube root of $114$ are missed by the full norm family (`ThreeCubes114.TernaryNorm.unbounded_normalized_moduli`). [Lean proof](TernaryFamily.lean) · [Norm formula](TernaryNorm.lean)

### Modular sieves and exact recovery

In [ThreeCubes114.lean](ThreeCubes114.lean), Lean kernel-checks the sieve conditions used for searching by pair sum $a = x + y$:

* `progression_congruences`: $(x + y) \equiv 1 \pmod 3$ and $x + y + z \equiv 0 \pmod{18}$.
* `ramified19_of_solution`: when $19 \mid (x + y)$, $(x + y)/19 \bmod 19$ must lie in 9 of the 19 classes (`[2, 3, 8, 10, 12, 13, 14, 15, 18]`), and `ramified19_local_witness` proves this characterizes the mod-$19^2$ obstruction.
* `even_pair_sieve`: an even pair sum admits only 8 combinations of $(x + y \bmod 32, z \bmod 8)$.
* `five_step_filter` and `five_example`: step filters when $5 \mid (x + y)$.
* `recoverPair_complete`: proves the exact integer square-root check recovers every solution.

## Reproduce

Run from this directory with Lean and mathlib pinned to **v4.36.0**:

```sh
lake exe cache get
lake build
```

To reproduce the search over 2,504,020 selected pair sums in the band $3M \le |z| < 51M$, run:

```sh
uv run TernaryOtherRoots.py --full
```

Lean checks in [NormCertificates.lean](NormCertificates.lean) that each of the 8 discriminants surviving the modular filters lies strictly between consecutive squares. [Search program](TernaryOtherRoots.py)

## References

* [Booker and Sutherland, `arXiv:2007.01209`, §5.2](https://arxiv.org/pdf/2007.01209#page=14)
* [Grantham and Walsh, `arXiv:2211.12149`](https://arxiv.org/abs/2211.12149)
* [Welsh, `arXiv:2008.00538`, Theorem 3](https://arxiv.org/abs/2008.00538)
* [Dated prior-art audit](../PRIOR_ART.md#three-integer-cubes-summing-to-114)
