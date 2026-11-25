# Reciprocal Rado number f_2(26) = 2028 (26 unit fractions, Gaiser–Ramezanpour Conjecture 1.3) — Lean 4 proof

**Exact value proved in Lean 4: $f_2(26) = 2028 = 3 \cdot 26^2$.** Color every integer in $\{1, 2, \ldots, N\}$ red or blue. Then **$N = 2028$** is the smallest endpoint that guarantees 27 monochromatic positive integers (with repeated denominators allowed) satisfying the 26-summand unit-fraction / Egyptian-fraction equation

$$
\frac{1}{x_1} + \frac{1}{x_2} + \cdots + \frac{1}{x_{26}} = \frac{1}{y}.
$$

This settles the $k = 26$ case of **Gaiser and Ramezanpour's Conjecture 1.3** (`arXiv:2607.04373`), which conjectures $f_2(k) = 3k^2$ (their July 2026 paper gives the lower bound, tabulates exact values through $k = 25$, and proves equality for $k = 3 \cdot 2^m$, leaving $k = 26$ as the first open case).

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Reciprocal Rado number** `f_2(26) = 2028` (`f₂(26) = 3 * 26^2`), 2-color unit-fraction / Egyptian-fraction Ramsey equation `1/x_1 + ... + 1/x_26 = 1/y` (repeated denominators allowed), Gaiser–Ramezanpour (`arXiv:2607.04373v1`) Conjecture 1.3 at $k = 26$ |
| **Status** | **Case $k = 26$ completely proved in Lean 4 ($f_2(26) = 2028$).** The general conjecture $f_2(k) = 3k^2$ for all $k$ remains open. |
| **Main Lean theorem** | `UnitFractions.forces_iff (N : Nat) : Forces N ↔ 2028 ≤ N` in [UnitFractions.lean](UnitFractions.lean) |
| **Verification** | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof, no mathlib) |
| **Prior-art status** | Checked **22 November 2026**: no earlier proof of the exact 26-summand upper bound located. The lower-bound coloring and initial forcing identities are published ingredients from Gaiser–Ramezanpour, and earlier Lean projects cover smaller $k$. See [PRIOR_ART.md](../PRIOR_ART.md#reciprocal-rado). |

## Proof overview

### Lower bound: why 2027 is too small ($f_2(26) \ge 2028$)

Color **3 through 77 red** and all other integers in $\{1, \ldots, 2027\}$ blue. If all 26 summand denominators are at most $M$, their sum is at least $26 / M$, so equality with $1 / y$ requires $26 y \le M$.

* **Red:** take $M = 77$. Then $y \le 2$, and both 1 and 2 are blue.
* **Blue:** take $M = 2027$. Then $y \le 77$, so a blue target can only be $y = 1$ or $y = 2$. Terms with denominator 1 or 2 sum to a multiple of $1/2$. The remaining blue denominators are at least 78, so they contribute at most $26 / 78 = 1/3$ — hence zero if the total is a multiple of $1/2$. That leaves 26 terms each at least $1/2$, far exceeding $1$ or $1/2$.

This is Gaiser and Ramezanpour's lower-bound coloring specialized to $k = 26$. [Theorem 1.1](https://arxiv.org/html/2607.04373v1#S2) · [Lean proof](UnitFractions/Lower.lean)

### Upper bound: why 2028 is enough ($f_2(26) \le 2028$)

Suppose a 2-coloring of $\{1, \ldots, 2028\}$ avoids every monochromatic solution. **Then $d$ and $26d$ have opposite colors** for every $d \ge 1$ with $26d \le 2028$, because 26 copies of $1/(26d)$ sum to $1/d$. Below, $m/d$ denotes $m$ copies of $1/d$.

Call the color of 3 red; then 78 is blue and 2028 is red. If 2 were blue, then 52 would be red; the first identity below would force 39 red, making the second identity all red. Therefore **2 and 3 are both red**, and 1352 is red as well:

$$
\frac{1}{2} = \frac{13}{39} + \frac{13}{78},
\qquad
\frac{1}{3} = \frac{12}{39} + \frac{1}{52} + \frac{13}{2028}.
$$

These two identities specialize Case 1 of Gaiser and Ramezanpour's proof of Theorem 3.3 to $k = 26$. [Theorem 3.3](https://arxiv.org/html/2607.04373v1#S3.Thmtheorem3)

Four further identities complete the contradiction at $k = 26$ (in each row, the right-hand numerators sum to 26, and all six identities clear denominators upon multiplying by 8112):

| Identity | Forced color |
| --- | --- |
| $1/2 = 1/3 + 2/13 + 6/1352 + 17/2028$ | 13 must be blue, so $26 \cdot 13 = 338$ is red. |
| $1/2 = 1/3 + 16/104 + 3/338 + 4/1352 + 2/2028$ | 104 must be blue, so $104 / 26 = 4$ is red. |
| $1/2 = 1/3 + 1/8 + 12/338 + 1/1352 + 11/2028$ | 8 must be blue, so $26 \cdot 8 = 208$ is red. |
| $1/3 = 1/4 + 16/208 + 8/1352 + 1/2028$ | Every denominator is red — contradiction. |

[Lean proof](UnitFractions/Upper.lean)

## Check the proof

Run from this directory with Lean **4.36.0** (uses only the Lean standard library):

```sh
lake build
```

The main theorem is `UnitFractions.forces_iff (N : Nat) : Forces N ↔ 2028 ≤ N`. [Theorem](UnitFractions.lean) · [Definition of a solution](UnitFractions/Basic.lean)

## References

* [Gaiser and Ramezanpour, `arXiv:2607.04373v1`: Conjecture 1.3](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem3) · [Theorem 1.2](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem2) · [Tables 1 and 2](https://arxiv.org/html/2607.04373v1#S3.T1)
* [Dated prior-art audit](../PRIOR_ART.md#reciprocal-rado)
